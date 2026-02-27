# PATH: type-gating-pipeline-model

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from existing code — `frontend/src/lib/file-content.ts`, `frontend/src/app/api/generate/route.ts`, `frontend/__tests__/lib/file-content.test.ts`, `frontend/__tests__/api/generate.test.ts`
**Parent models:** `file-to-llm-pipeline-model`, `file-to-llm-pipeline-target`

## Purpose

Behavioral model of the MIME type-gating and content conversion subsystem within
the chat attachment-to-LLM pipeline. This model captures the three serial gates
a file must pass to reach the LLM, the conversion branches that transform file
content into API-consumable format, and the structural fragilities that will
break when new document types are added.

This is a sub-slice of the umbrella pipeline models. It covers:
- Frontend MIME gate (`isSupportedMimeType`)
- Frontend content conversion (`prepareFileContent`)
- Server-side MIME gate (`isSupportedAttachment`)
- Server-side content assembly (`buildUserContent`)
- The dual-whitelist consistency hazard
- The unguarded catch-all text branch

Out of scope: backend `/api/files/upload` (separate subsystem, not in the chat send path),
FileAttachment UI validation (size/count only, no MIME check), HTML `accept` attribute
(UX affordance, not safety gate).

## Trigger

User attaches a file and sends a message. The file's MIME type must survive
three serial gates and be converted to a format the OpenAI Responses API can
consume (`input_text` or `input_image`).

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `fn-g1a1` | frontend_gate | `isSupportedMimeType()` at file-content.ts:22 |
| `fn-g1b2` | frontend_prep | `prepareFileContent()` at file-content.ts:98 |
| `fn-g1c3` | frontend_batch | `prepareFilesContent()` at file-content.ts:123 |
| `fn-g2a4` | route_gate | `isSupportedAttachment()` at route.ts:113 |
| `fn-g2b5` | route_assembly | `buildUserContent()` at route.ts:129 |
| `cfg-w1s6` | fe_image_set | `SUPPORTED_IMAGE_TYPES` at file-content.ts:10 |
| `cfg-w1t7` | fe_text_set | `SUPPORTED_TEXT_TYPES` at file-content.ts:17 |
| `cfg-w2s8` | rt_image_set | `SUPPORTED_IMAGE_TYPES` at route.ts:56 |
| `cfg-w2t9` | rt_text_set | `SUPPORTED_TEXT_TYPES` at route.ts:57 |
| `api-r1p0` | response_part | `ResponseInputPart` union at route.ts:47-49 |

## State Variables

```
mimeType           : STRING              \* file.type as read from browser
mimeCategory       : {correct, empty, aliased, rejected}
                                         \* classification of the raw MIME value
gate1Result        : {pass_image, pass_text, reject}
                                         \* outcome of frontend isSupportedMimeType()
conversionBranch   : {image_dataurl, text_readastext, catch_all_text, none}
                                         \* which branch of prepareFileContent runs
payloadShape       : {base64Data, textContent, none}
                                         \* which field is populated on FileContentPayload
gate2Result        : {pass_image, pass_text, silent_drop}
                                         \* outcome of route isSupportedAttachment()
assemblyOutput     : {plain_string, text_prefixed_string, input_parts_array, dropped}
                                         \* return type of buildUserContent
llmContentType     : {input_text, input_image, absent}
                                         \* what the LLM actually receives
```

## Steps

1. **mime_resolved** — Browser provides file.type for the selected file

   - Input: File object from user selection or drag-and-drop
   - Process: Read `file.type` property. Browser determines MIME from file extension and OS metadata. No normalization is applied by any code in this pipeline — no lowercasing, no trimming, no alias resolution.
   - Output: Raw `mimeType` string. Classified into `mimeCategory`:
     - `correct` — browser returns a standard MIME string matching the file format
     - `empty` — browser returns `""` for unknown extensions or unresolvable types
     - `aliased` — browser returns a valid but variant MIME (e.g., `application/csv` instead of `text/csv`)
     - `rejected` — any string not in either gate's whitelist
   - Error: None. `file.type` always returns a string (possibly empty).

2. **frontend_gate_checked** — Gate 1: `isSupportedMimeType()` at file-content.ts:22

   - Input: `mimeType` string from step 1
   - Process: Exact string lookup against two `Set` literals:
     - `SUPPORTED_IMAGE_TYPES`: `{image/png, image/jpeg, image/gif, image/webp}` at file-content.ts:10-15
     - `SUPPORTED_TEXT_TYPES`: `{text/plain, application/json}` at file-content.ts:17-20
     - Short-circuit OR: image set checked first, text set checked only if image misses
     - No normalization, no prefix matching, no alias resolution
   - Output: `gate1Result`:
     - `pass_image` — mimeType is in SUPPORTED_IMAGE_TYPES
     - `pass_text` — mimeType is in SUPPORTED_TEXT_TYPES (but not image set)
     - `reject` — mimeType is in neither set
   - Error: On `reject`, `prepareFileContent` at file-content.ts:102-103 throws `UnsupportedFileError(filename, mimeType)`. This is a hard rejection — batch aborts, `generateResponse` is never called. Error surfaces to user via `page.tsx:72 mapAttachmentError`.

3. **content_converted** — `prepareFileContent()` reads file bytes at file-content.ts:106-120

   - Input: File object, `gate1Result` from step 2 (must be `pass_image` or `pass_text`)
   - Process: Branches on `SUPPORTED_IMAGE_TYPES.has(contentType)` at line 106:
     - **Image branch (explicit check):** `readAsDataURL(file)` → produces `data:<mime>;base64,<encoded>` string. Sets `payloadShape = base64Data`.
     - **Catch-all branch (NO check for SUPPORTED_TEXT_TYPES):** If the image check fails, execution falls through unconditionally to `readAsText(file)` at line 115. Sets `payloadShape = textContent`.
   - Output: `FileContentPayload` with `{ filename, contentType, textContent? | base64Data? }`. The `contentType` field preserves the original MIME string — no transformation.
   - Error: `FileReader` failure produces `DOMException` or `Error('Failed to read file as ...')`.

   **STRUCTURAL FRAGILITY (see TG-3):** The text branch is an unguarded catch-all. Today this is safe because Gate 1's whitelist is the exact union of image + text sets — only `text/plain` and `application/json` reach the catch-all. But if a new type (e.g., `application/pdf`) is added to Gate 1 without also adding a dedicated branch, it silently falls through to `readAsText()` and produces garbage. No error is thrown — corrupt data reaches the API.

4. **batch_iterated** — `prepareFilesContent()` processes files sequentially at file-content.ts:123-131

   - Input: Array of File objects
   - Process: Sequential `for` loop. Each file passes through steps 2-3. `await` on each before advancing. Results pushed to array in input order.
   - Output: `FileContentPayload[]` preserving input ordering
   - Error: Fail-fast on first rejection. Remaining files are not processed. Error propagates unwrapped to `page.tsx` caller.

5. **request_serialized** — `generateResponse()` at api.ts builds JSON body

   - Input: message string, conversation history, `FileContentPayload[]` from step 4
   - Process: Builds `{ message, history: last10, attachments }` and POSTs to `/api/generate`. Attachments carry original `contentType` strings unchanged.
   - Output: JSON request body with attachments array
   - Error: Network failure or non-ok response.

6. **route_gate_checked** — Gate 2: `isSupportedAttachment()` at route.ts:113, applied via `.filter()` at route.ts:133

   - Input: `FileAttachment` objects parsed from request body by `parseAttachments()` at route.ts:103
   - Process: Exact string lookup against two independently-declared `Set` literals:
     - `SUPPORTED_IMAGE_TYPES`: `{image/png, image/jpeg, image/gif, image/webp}` at route.ts:56
     - `SUPPORTED_TEXT_TYPES`: `{text/plain, application/json}` at route.ts:57
     - Same structure as Gate 1, but **separate declaration** — no shared import
   - Output: `gate2Result`:
     - `pass_image` — contentType in route's SUPPORTED_IMAGE_TYPES
     - `pass_text` — contentType in route's SUPPORTED_TEXT_TYPES
     - `silent_drop` — contentType in neither set. **Attachment is removed from `supported` array with no error, no log, no user notification.** Request continues.
   - Error: None. Silent filtering only.

   **ORDERING ANOMALY:** `calculatePayloadSize()` at route.ts:188 runs on ALL parsed attachments (including types that Gate 2 will later drop) before `buildUserContent` applies the MIME filter at route.ts:205/133. A large unsupported attachment counts toward the 25MB cap and can trigger `PAYLOAD_TOO_LARGE` even though its content would be discarded.

7. **content_assembled** — `buildUserContent()` at route.ts:129-163

   - Input: message string, `supported` attachments array (post-Gate 2 filter)
   - Process: Re-partitions `supported` into text and image sub-lists using the same sets:
     - `textAttachments = supported.filter(a => SUPPORTED_TEXT_TYPES.has(a.contentType))` at line 138
     - `imageAttachments = supported.filter(a => SUPPORTED_IMAGE_TYPES.has(a.contentType))` at line 139
     - This re-partition is exhaustive over the current 6-type whitelist
   - Output: `string | ResponseInputPart[]` — one of four shapes depending on partition contents: plain message string when no supported attachments remain, text-prefixed string when text-only attachments present, input_parts array with input_text and input_image entries when images present, or mixed array combining text prefix with image parts
   - Error: None. `buildUserContent` does not throw.

   **TYPE CONSTRAINT (TG-7):** `ResponseInputPart` union at route.ts:47-49 has exactly two variants: `input_text` and `input_image`. There is no third variant for binary document content. Server-side text extraction feeding into `input_text` is the only viable path for new document types.

8. **delivered_to_llm** — Content placed in OpenAI input array at route.ts:213

   - Input: `string | ResponseInputPart[]` from step 7
   - Process: Set as `content` field on `{ role: 'user', content: userContent }` in the input array passed to `generateWithRetry`
   - Output: OpenAI receives either a plain string or a multipart content array
   - Error: None at this step. Errors from OpenAI are handled by the retry logic in the parent pipeline model.

## Terminal Condition

**Success:** File content reaches OpenAI as `input_text` (for text types) or `input_image` (for image types). LLM response is informed by the file content.

**Gate 1 rejection:** `UnsupportedFileError` thrown. Batch aborted. No API call made. User sees error message naming the rejected file.

**Gate 2 silent drop:** Attachment removed from `supported` array. If it was the only attachment, `buildUserContent` returns plain message string. User sees no error — file was silently discarded. LLM response is not informed by the file.

**Garbage pass-through (latent):** If a binary type is added to Gate 1 without a dedicated conversion branch, `readAsText()` produces corrupt content that passes through Gate 2 (if also added there) and reaches the LLM as garbled `input_text`.

## Feedback Loops

None. This is a strictly linear pipeline with no retry or iteration semantics. Retry logic is in the parent pipeline model at the OpenAI call step.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Status |
|----|-----------|--------|---------------|--------|
| TG-1 | Gate 1 whitelist (file-content.ts:10-20) and Gate 2 whitelist (route.ts:56-57) must contain the same set of MIME types | Independent Set declarations, no shared import | `WhitelistConsistency` | **FRAGILE** — holds today by coincidence, no compile-time or runtime check, can drift silently when new types are added |
| TG-2 | Every MIME type that passes Gate 1 must also pass Gate 2 (Gate1 ⊆ Gate2) | Structural consequence of TG-1 | `GateSubset` | HOLDS today. Violation means files pass frontend prep, get serialized and transmitted, then silently dropped server-side |
| TG-3 | Every type that passes Gate 1 and is not in SUPPORTED_IMAGE_TYPES must produce valid UTF-8 when read with readAsText() | file-content.ts:106-120 — catch-all text branch has no SUPPORTED_TEXT_TYPES guard | `CatchAllSafety` | **STRUCTURALLY FRAGILE** — holds today because Gate 1 whitelist = image ∪ text exactly. Adding any non-text type to Gate 1 (e.g., application/pdf) causes silent garbage: readAsText on binary produces corrupt data, no error thrown |
| TG-4 | buildUserContent re-partition (text + image sub-lists) is exhaustive over all types that pass Gate 2 | route.ts:138-141 re-queries same sets used by isSupportedAttachment | `PartitionExhaustive` | HOLDS today — every type in Gate 2 whitelist is in exactly one of the two sub-sets |
| TG-5 | readAsText produces valid UTF-8 for every type routed to the catch-all text branch | file-content.ts:115 readAsText on the file | `TextReadValidity` | HOLDS for text/plain, application/json. WOULD FAIL for binary formats (pdf, docx, xlsx, xls, doc) |
| TG-6 | readAsDataURL produces a data URL consumable as input_image for every type routed to the image branch | file-content.ts:107 readAsDataURL on the file | `ImageReadValidity` | HOLDS for image/{png,jpeg,gif,webp}. WOULD FAIL for non-image binary formats |
| TG-7 | ResponseInputPart union has exactly two variants: input_text and input_image. No third variant exists for binary document blobs. | route.ts:47-49 type definition | `PartTypeCompleteness` | HOLDS — architectural constraint. Server-side text extraction to input_text is the only viable path for new document types. |
| TG-8 | Unsupported types at Gate 1 cause hard rejection (UnsupportedFileError thrown, batch aborted) | file-content.ts:102-103 | `Gate1HardReject` | HOLDS — test at file-content.test.ts:38 asserts PDF rejection |
| TG-9 | Unsupported types at Gate 2 cause silent drop (no error, attachment removed from supported array) | route.ts:133 .filter() | `Gate2SilentDrop` | HOLDS — test at generate.test.ts:68 asserts PDF silently skipped |
| TG-10 | Payload size check at route.ts:188 runs on all parsed attachments including those Gate 2 will later drop | route.ts:188 before route.ts:205 | `PayloadSizeOrdering` | HOLDS — ordering anomaly: large unsupported files count toward 25MB cap then get discarded |

## Type Categories for Proposed Change

| Category | Types | Conversion path | Gate changes needed |
|----------|-------|-----------------|---------------------|
| Already works | `text/plain` | Existing text readAsText → input_text | None |
| Text-readable, gate-only change | `text/csv` | Existing readAsText → input_text (CSV is plain UTF-8) | Add to both whitelists (file-content.ts + route.ts) and route.ts SUPPORTED_TEXT_TYPES |
| Binary, needs server extraction | `application/pdf`, `application/msword`, `application/vnd.openxmlformats-officedocument.wordprocessingml.document`, `application/vnd.ms-excel`, `application/vnd.openxmlformats-officedocument.spreadsheetml.sheet` | New extraction pipeline: client uploads blob → server extracts text → feeds into input_text | Both whitelists + new conversion branch in prepareFileContent + new extraction step in route + new SUPPORTED_DOCUMENT_TYPES set |

### MIME Alias Note

`text/csv` is the standard MIME for .csv files. Browsers consistently report .csv as `text/csv`. However, `application/csv` is a valid alias in some contexts (programmatic uploads, third-party tools). If MIME normalization is implemented, CSV is a concrete test case for the `mimeAliased` state.

## Change Impact Analysis

**Proposed change:** File upload supports .txt, .doc/.docx, .pdf, .csv, .xls/.xlsx end-to-end through the chat attachment-to-LLM path.

**Affected invariants:**

| Invariant | Impact |
|-----------|--------|
| TG-1 (WhitelistConsistency) | **HIGH RISK** — must add identical types to both independently-declared whitelists. Recommend extracting to shared constant. |
| TG-2 (GateSubset) | **HIGH RISK** — if Gate 1 is updated but Gate 2 is missed, files silently reach server then get dropped. No user-visible error. |
| TG-3 (CatchAllSafety) | **CRITICAL** — adding binary types to Gate 1 without a new branch causes them to fall through to readAsText, producing garbage that reaches the LLM. Must add explicit branching for new type category before gate expansion. |
| TG-4 (PartitionExhaustive) | **MUST UPDATE** — new types need to land in one of the route.ts sub-partitions or a new one |
| TG-5 (TextReadValidity) | SAFE for text/csv. **WOULD BREAK** if binary types route to readAsText. |
| TG-6 (ImageReadValidity) | Unaffected — no new image types proposed |
| TG-7 (PartTypeCompleteness) | Constrains solution: server-side text extraction to input_text is required. No new ResponseInputPart variant. |
| TG-8 (Gate1HardReject) | Semantics change for newly-supported types: they must pass, not reject. Test at file-content.test.ts:38 must be updated. |
| TG-9 (Gate2SilentDrop) | Semantics change for newly-supported types: they must pass, not drop. Test at generate.test.ts:68 must be updated. |
| TG-10 (PayloadSizeOrdering) | Unaffected but worth noting: binary documents may be large. |

**Risk ordering:**
1. TG-3 is the highest risk. Binary types falling through to readAsText is a silent data corruption bug with no error signal.
2. TG-1/TG-2 are the second risk. Dual-whitelist drift causes silent feature failure.
3. TG-8/TG-9 test updates are mechanical but forgetting them causes CI failures that block the change.

**Recommendation:** Implement conversion branch changes (TG-3 fix) before expanding any whitelists. The branch must explicitly handle the new document category and reject or route unknown types — replacing the catch-all with a checked partition.

## TLA+ Specification

```tla
---------------------------- MODULE TypeGatingPipeline ----------------------------
\* Behavioral model of the MIME type-gating subsystem for chat attachments
\* Sub-slice of FileToLlmPipeline — covers gates, conversion, and assembly
\* Three structural fragilities documented: TG-1, TG-2, TG-3

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    ImageMimeTypes,      \* Set of MIME strings in SUPPORTED_IMAGE_TYPES
    TextMimeTypes,       \* Set of MIME strings in SUPPORTED_TEXT_TYPES
    DocumentMimeTypes,   \* Set of binary document MIME types (proposed addition)
    CsvMimeType,         \* "text/csv" — text-readable, gate-only change
    AllMimeTypes,        \* Universe of possible MIME strings including empty
    EMPTY_MIME,          \* "" — browser returns this for unknown extensions
    NULL                 \* Null sentinel

VARIABLES
    \* --- Input ---
    mimeType,            \* Raw MIME string from file.type
    mimeCategory,        \* Classification: correct, empty, aliased, rejected

    \* --- Gate 1 (frontend) ---
    feImageSet,          \* Current contents of file-content.ts SUPPORTED_IMAGE_TYPES
    feTextSet,           \* Current contents of file-content.ts SUPPORTED_TEXT_TYPES
    gate1Result,         \* pass_image, pass_text, reject

    \* --- Conversion ---
    conversionBranch,    \* image_dataurl, text_readastext, catch_all_fallthrough, none
    payloadShape,        \* base64Data, textContent, garbage, none
    contentType,         \* MIME string preserved on FileContentPayload

    \* --- Gate 2 (route) ---
    rtImageSet,          \* Current contents of route.ts SUPPORTED_IMAGE_TYPES
    rtTextSet,           \* Current contents of route.ts SUPPORTED_TEXT_TYPES
    gate2Result,         \* pass_image, pass_text, silent_drop

    \* --- Assembly ---
    assemblyOutput,      \* plain_string, text_prefixed_string, input_parts_array, dropped
    llmContentType,      \* input_text, input_image, absent

    \* --- Pipeline phase ---
    phase                \* Current step in the pipeline

vars == <<mimeType, mimeCategory, feImageSet, feTextSet, gate1Result,
          conversionBranch, payloadShape, contentType,
          rtImageSet, rtTextSet, gate2Result,
          assemblyOutput, llmContentType, phase>>

Phase == {"idle", "mime_resolved", "frontend_gate_checked",
          "content_converted", "route_gate_checked",
          "content_assembled", "delivered", "rejected", "dropped"}

MimeCategory == {"correct", "empty", "aliased", "rejected"}
Gate1Result == {"pass_image", "pass_text", "reject"}
ConversionBranch == {"image_dataurl", "text_readastext", "catch_all_fallthrough", "none"}
PayloadShape == {"base64Data", "textContent", "garbage", "none"}
Gate2Result == {"pass_image", "pass_text", "silent_drop"}
AssemblyOutput == {"plain_string", "text_prefixed_string", "input_parts_array", "dropped"}
LlmContentType == {"input_text", "input_image", "absent"}

\* ===========================================================================
\* Initial state
\* ===========================================================================

Init ==
    /\ mimeType = NULL
    /\ mimeCategory = "correct"
    /\ feImageSet = ImageMimeTypes
    /\ feTextSet = TextMimeTypes
    /\ gate1Result = "reject"
    /\ conversionBranch = "none"
    /\ payloadShape = "none"
    /\ contentType = NULL
    /\ rtImageSet = ImageMimeTypes       \* Starts identical to frontend (TG-1)
    /\ rtTextSet = TextMimeTypes         \* Starts identical to frontend (TG-1)
    /\ gate2Result = "silent_drop"
    /\ assemblyOutput = "dropped"
    /\ llmContentType = "absent"
    /\ phase = "idle"

\* ===========================================================================
\* Step 1: mime_resolved — Browser provides file.type
\* Source: file.type property, no normalization in pipeline
\* ===========================================================================

ResolveMime(mime) ==
    /\ phase = "idle"
    /\ mimeType' = mime
    /\ mimeCategory' = CASE mime = EMPTY_MIME -> "empty"
                          [] mime \in (feImageSet \union feTextSet) -> "correct"
                          [] OTHER -> "rejected"
       \* Note: "aliased" would require a normalization map not present in code
    /\ phase' = "mime_resolved"
    /\ UNCHANGED <<feImageSet, feTextSet, gate1Result, conversionBranch,
                   payloadShape, contentType, rtImageSet, rtTextSet,
                   gate2Result, assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 2: frontend_gate_checked — Gate 1: isSupportedMimeType()
\* Source: file-content.ts:22 — OR of two Set.has() checks
\* ===========================================================================

FrontendGateCheck ==
    /\ phase = "mime_resolved"
    /\ IF mimeType \in feImageSet
       THEN /\ gate1Result' = "pass_image"
            /\ phase' = "frontend_gate_checked"
       ELSE IF mimeType \in feTextSet
            THEN /\ gate1Result' = "pass_text"
                 /\ phase' = "frontend_gate_checked"
            ELSE /\ gate1Result' = "reject"
                 /\ phase' = "rejected"  \* TG-8: hard rejection
    /\ UNCHANGED <<mimeType, mimeCategory, feImageSet, feTextSet,
                   conversionBranch, payloadShape, contentType,
                   rtImageSet, rtTextSet, gate2Result,
                   assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 3: content_converted — prepareFileContent() reads file bytes
\* Source: file-content.ts:106-120
\*
\* CRITICAL: The text branch is an UNGUARDED CATCH-ALL.
\* Line 106 checks SUPPORTED_IMAGE_TYPES.has() explicitly.
\* Line 115 has NO check — anything not-image falls through to readAsText().
\* ===========================================================================

ConvertContent ==
    /\ phase = "frontend_gate_checked"
    /\ contentType' = mimeType   \* Original MIME preserved on payload
    /\ IF mimeType \in feImageSet
       THEN \* Explicit image branch (line 106)
            /\ conversionBranch' = "image_dataurl"
            /\ payloadShape' = "base64Data"
       ELSE \* CATCH-ALL: no SUPPORTED_TEXT_TYPES.has() guard (line 115)
            \* Everything that passed Gate 1 and is not image lands here
            /\ IF mimeType \in feTextSet
               THEN \* Safe: readAsText on actual text produces valid UTF-8
                    /\ conversionBranch' = "text_readastext"
                    /\ payloadShape' = "textContent"
               ELSE \* FRAGILE: non-text type fell through catch-all
                    \* readAsText on binary produces garbage, no error
                    /\ conversionBranch' = "catch_all_fallthrough"
                    /\ payloadShape' = "garbage"
    /\ phase' = "content_converted"
    /\ UNCHANGED <<mimeType, mimeCategory, feImageSet, feTextSet, gate1Result,
                   rtImageSet, rtTextSet, gate2Result,
                   assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 4: route_gate_checked — Gate 2: isSupportedAttachment()
\* Source: route.ts:113, applied via .filter() at route.ts:133
\* Uses INDEPENDENTLY DECLARED whitelists at route.ts:56-57
\* ===========================================================================

RouteGateCheck ==
    /\ phase = "content_converted"
    /\ IF contentType \in rtImageSet
       THEN /\ gate2Result' = "pass_image"
            /\ phase' = "route_gate_checked"
       ELSE IF contentType \in rtTextSet
            THEN /\ gate2Result' = "pass_text"
                 /\ phase' = "route_gate_checked"
            ELSE /\ gate2Result' = "silent_drop"  \* TG-9: no error, no log
                 /\ phase' = "dropped"
    /\ UNCHANGED <<mimeType, mimeCategory, feImageSet, feTextSet, gate1Result,
                   conversionBranch, payloadShape, contentType,
                   rtImageSet, rtTextSet, assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 5: content_assembled — buildUserContent() at route.ts:129
\* Re-partitions into text and image sub-lists
\* ===========================================================================

AssembleContent ==
    /\ phase = "route_gate_checked"
    /\ IF gate2Result = "pass_text"
       THEN /\ assemblyOutput' = "text_prefixed_string"
            /\ llmContentType' = "input_text"
       ELSE IF gate2Result = "pass_image"
            THEN /\ assemblyOutput' = "input_parts_array"
                 /\ llmContentType' = "input_image"
            ELSE \* Should not reach here — gate2Result is pass_* at this phase
                 /\ assemblyOutput' = "dropped"
                 /\ llmContentType' = "absent"
    /\ phase' = "content_assembled"
    /\ UNCHANGED <<mimeType, mimeCategory, feImageSet, feTextSet, gate1Result,
                   conversionBranch, payloadShape, contentType,
                   rtImageSet, rtTextSet, gate2Result>>

\* ===========================================================================
\* Step 6: delivered_to_llm — Content placed in OpenAI input array
\* Source: route.ts:213
\* ===========================================================================

DeliverToLlm ==
    /\ phase = "content_assembled"
    /\ phase' = "delivered"
    /\ UNCHANGED <<mimeType, mimeCategory, feImageSet, feTextSet, gate1Result,
                   conversionBranch, payloadShape, contentType,
                   rtImageSet, rtTextSet, gate2Result,
                   assemblyOutput, llmContentType>>

\* ===========================================================================
\* Next-state relation
\* ===========================================================================

Next ==
    \/ \E m \in AllMimeTypes : ResolveMime(m)
    \/ FrontendGateCheck
    \/ ConvertContent
    \/ RouteGateCheck
    \/ AssembleContent
    \/ DeliverToLlm

Spec == Init /\ [][Next]_vars

\* ===========================================================================
\* INVARIANTS
\* ===========================================================================

\* --- TG-1: WhitelistConsistency ---
\* The two independently-declared whitelists must be identical.
\* FRAGILE: no shared import enforces this at compile time.
WhitelistConsistency ==
    /\ feImageSet = rtImageSet
    /\ feTextSet = rtTextSet

\* --- TG-2: GateSubset ---
\* Every type that passes Gate 1 must also pass Gate 2.
\* Violation means files are serialized, transmitted, then silently dropped.
GateSubset ==
    (feImageSet \union feTextSet) \subseteq (rtImageSet \union rtTextSet)

\* --- TG-3: CatchAllSafety ---
\* Every type that reaches the catch-all text branch must produce valid text.
\* The catch-all runs for anything in Gate 1 whitelist minus SUPPORTED_IMAGE_TYPES.
\* FRAGILE: currently safe only because (Gate1 \ ImageSet) = TextSet exactly.
CatchAllSafety ==
    (feImageSet \union feTextSet) \ feImageSet = feTextSet
    \* If this fails, there exist types that pass Gate 1, miss the image check,
    \* and fall through to readAsText without being actual text types.

\* --- TG-3b: No garbage reaches the LLM ---
\* If the catch-all branch produced garbage, it must not reach delivery.
NoGarbageDelivery ==
    phase = "delivered" => payloadShape /= "garbage"

\* --- TG-4: PartitionExhaustive ---
\* Every type that passes Gate 2 lands in exactly one sub-partition
\* (text or image) in buildUserContent.
PartitionExhaustive ==
    phase = "route_gate_checked" =>
        \/ gate2Result = "pass_text"
        \/ gate2Result = "pass_image"

\* --- TG-5: TextReadValidity ---
\* readAsText on text-branch types produces valid content.
\* Modeled: if conversionBranch is text_readastext, payloadShape must be textContent (not garbage).
TextReadValidity ==
    conversionBranch = "text_readastext" => payloadShape = "textContent"

\* --- TG-6: ImageReadValidity ---
\* readAsDataURL on image-branch types produces valid content.
ImageReadValidity ==
    conversionBranch = "image_dataurl" => payloadShape = "base64Data"

\* --- TG-7: PartTypeCompleteness ---
\* LLM content type is always input_text or input_image when delivered.
\* No third variant exists in ResponseInputPart.
PartTypeCompleteness ==
    phase = "delivered" => llmContentType \in {"input_text", "input_image"}

\* --- TG-8: Gate1HardReject ---
\* Unsupported types at Gate 1 cause hard rejection (phase goes to "rejected").
Gate1HardReject ==
    gate1Result = "reject" => phase \in {"rejected", "mime_resolved", "idle"}

\* --- TG-9: Gate2SilentDrop ---
\* Unsupported types at Gate 2 cause silent drop (phase goes to "dropped").
Gate2SilentDrop ==
    gate2Result = "silent_drop" => phase \in {"dropped", "content_converted", "idle"}

\* --- TG-10: End-to-end delivery ---
\* A type reaches the LLM only if it passed both gates AND was correctly converted.
EndToEndDelivery ==
    phase = "delivered" =>
        /\ gate1Result \in {"pass_image", "pass_text"}
        /\ gate2Result \in {"pass_image", "pass_text"}
        /\ payloadShape \in {"base64Data", "textContent"}

\* ===========================================================================
\* LIVENESS
\* ===========================================================================

\* Every file eventually reaches a terminal state
EventualTermination == <>(phase \in {"delivered", "rejected", "dropped"})

\* ===========================================================================
\* TARGET INVARIANTS (what SHOULD hold after the change)
\* ===========================================================================

\* TARGET-TG-1: Whitelists are a single shared source of truth
\* TargetWhitelistConsistency ==
\*     \* Structural fix: single import, not duplicate declarations
\*     WhitelistConsistency  \* Same predicate but enforced by code structure

\* TARGET-TG-3: Catch-all replaced with checked partition
\* TargetCheckedPartition ==
\*     \* No type reaches catch_all_fallthrough — every branch is explicit
\*     conversionBranch /= "catch_all_fallthrough"

\* TARGET-TG-CSV: text/csv passes both gates and routes to text path
\* TargetCsvSupport ==
\*     mimeType = CsvMimeType =>
\*         (phase = "delivered" =>
\*             /\ gate1Result = "pass_text"
\*             /\ gate2Result = "pass_text"
\*             /\ payloadShape = "textContent"
\*             /\ llmContentType = "input_text")

\* TARGET-TG-DOC: Binary document types pass both gates and route to extraction
\* TargetDocumentSupport ==
\*     mimeType \in DocumentMimeTypes =>
\*         (phase = "delivered" =>
\*             /\ gate1Result \in {"pass_document"}  \* New gate result
\*             /\ gate2Result \in {"pass_document"}  \* New gate result
\*             /\ payloadShape = "textContent"        \* After server extraction
\*             /\ llmContentType = "input_text")      \* Feeds existing path

=============================================================================
```

## Relationship to Parent Models

This model is a sub-slice of:
- **file-to-llm-pipeline-model.md** — steps 1 (files_selected) and 5 (file_content_prepared) in that model decompose into this model's full 8-step sequence
- **file-to-llm-pipeline-target.md** — step 5 (file_content_prepared) assumed files could be read; this model reveals the structural fragility (TG-3) that makes that assumption unsafe for binary document types

The parent model's INV-2 (FileContentDelivery) depends on this model's TG-2 (GateSubset) — if Gate 2 silently drops a type, the parent's multipart content construction never sees it.
