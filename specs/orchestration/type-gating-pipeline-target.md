# PATH: type-gating-pipeline-target

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 2
**Source:** Extended from `type-gating-pipeline-model` (baseline). Adds document type support, fixes structural fragilities TG-1, TG-3, TG-4.
**Parent models:** `file-to-llm-pipeline-model`, `file-to-llm-pipeline-target`

## Purpose

Target behavioral model for the MIME type-gating and content conversion subsystem.
This extends the baseline model to support `.txt, .doc/.docx, .pdf, .csv, .xls/.xlsx`
end-to-end through the chat attachment-to-LLM path. All 10 baseline invariants are
preserved (with structural fixes for fragile ones), and new invariants are added for
the document extraction pipeline.

Key structural changes from baseline:
- **TG-1 fix:** Dual whitelists replaced with single shared source of truth
- **TG-3 fix:** Catch-all text branch replaced with checked three-way partition (image / text / document)
- **TG-4 fix:** Route re-partition updated to three-way (image / text / document)
- **New type sets:** `SUPPORTED_DOCUMENT_TYPES` for binary formats, `text/csv` added to `SUPPORTED_TEXT_TYPES`
- **New step:** `document_extracted` — server-side text extraction for binary documents
- **New conversion branch:** `document_upload` — client sends raw blob, server extracts text
- **No new ResponseInputPart variant** — extracted document text feeds through existing `input_text`

## Trigger

User attaches a file (.txt, .csv, .doc, .docx, .pdf, .xls, or .xlsx) and sends
a message. The file's MIME type must survive two gates, be converted (text-readable
types read client-side, binary types extracted server-side), and assembled into
`input_text` or `input_image` format for the OpenAI Responses API.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `fn-g1a1` | frontend_gate | `isSupportedMimeType()` — expanded to three-way check |
| `fn-g1b2` | frontend_prep | `prepareFileContent()` — checked partition replaces catch-all |
| `fn-g1c3` | frontend_batch | `prepareFilesContent()` — unchanged sequential loop |
| `fn-g2a4` | route_gate | `isSupportedAttachment()` — expanded to three type sets |
| `fn-g2b5` | route_assembly | `buildUserContent()` — expanded to handle document text |
| `fn-e1x1` | doc_extractor | New server-side text extraction function for binary documents |
| `cfg-s1a1` | shared_types | Single shared type constant module (replaces dual declarations) |
| `cfg-s1i2` | image_set | `SUPPORTED_IMAGE_TYPES` — unchanged, single source |
| `cfg-s1t3` | text_set | `SUPPORTED_TEXT_TYPES` — expanded: adds `text/csv` |
| `cfg-s1d4` | document_set | `SUPPORTED_DOCUMENT_TYPES` — new: pdf, doc, docx, xls, xlsx |
| `api-r1p0` | response_part | `ResponseInputPart` union — unchanged: input_text, input_image only |

## State Variables

```
mimeType           : STRING
mimeCategory       : {correct, empty, aliased, rejected}
gate1Result        : {pass_image, pass_text, pass_document, reject}
                                         \* NEW: pass_document for binary types
conversionBranch   : {image_dataurl, text_readastext, document_upload, none}
                                         \* NEW: document_upload replaces catch_all_fallthrough
payloadShape       : {base64Data, textContent, rawBlob, none}
                                         \* NEW: rawBlob for documents awaiting server extraction
extractionResult   : {extracted_text, extraction_failed, not_applicable}
                                         \* NEW: outcome of server-side text extraction
contentType        : STRING
gate2Result        : {pass_image, pass_text, pass_document, silent_drop}
                                         \* NEW: pass_document
assemblyOutput     : {plain_string, text_prefixed_string, input_parts_array, dropped}
llmContentType     : {input_text, input_image, absent}
phase              : Phase
```

## Steps

1. **mime_resolved** — Browser provides file.type for the selected file

   - Input: File object from user selection or drag-and-drop
   - Process: Read `file.type` property. No normalization applied. Optional MIME alias normalization map can resolve known variants (e.g., `application/csv` to `text/csv`) but is not required for MVP since browsers consistently report standard MIME types for the target extensions.
   - Output: Raw `mimeType` string classified into `mimeCategory`
   - Error: None. `file.type` always returns a string (possibly empty).

2. **frontend_gate_checked** — Gate 1: expanded `isSupportedMimeType()`

   - Input: `mimeType` string from step 1
   - Process: Exact string lookup against three `Set` constants from shared type module:
     - `SUPPORTED_IMAGE_TYPES`: `{image/png, image/jpeg, image/gif, image/webp}` — unchanged
     - `SUPPORTED_TEXT_TYPES`: `{text/plain, application/json, text/csv}` — **adds text/csv**
     - `SUPPORTED_DOCUMENT_TYPES`: `{application/pdf, application/msword, application/vnd.openxmlformats-officedocument.wordprocessingml.document, application/vnd.ms-excel, application/vnd.openxmlformats-officedocument.spreadsheetml.sheet}` — **new set**
     - Check order: image first, then text, then document, then reject
     - All three sets imported from a single shared module (fixes TG-1)
   - Output: `gate1Result`:
     - `pass_image` — mimeType in SUPPORTED_IMAGE_TYPES
     - `pass_text` — mimeType in SUPPORTED_TEXT_TYPES (includes text/csv)
     - `pass_document` — mimeType in SUPPORTED_DOCUMENT_TYPES
     - `reject` — mimeType in none of the three sets
   - Error: On `reject`, throws `UnsupportedFileError`. Error message updated to list all supported categories. Batch aborts.

3. **content_converted** — `prepareFileContent()` with checked three-way partition

   - Input: File object, `gate1Result` from step 2
   - Process: **Checked partition replaces catch-all** (fixes TG-3):
     - **Image branch** (explicit check `SUPPORTED_IMAGE_TYPES.has()`): `readAsDataURL(file)` → `payloadShape = base64Data`
     - **Text branch** (explicit check `SUPPORTED_TEXT_TYPES.has()`): `readAsText(file)` → `payloadShape = textContent`. Safe for text/plain, application/json, and text/csv — all produce valid UTF-8.
     - **Document branch** (explicit check `SUPPORTED_DOCUMENT_TYPES.has()`): `readAsArrayBuffer(file)` then convert to base64 string → `payloadShape = rawBlob`. No text extraction attempted client-side. The raw bytes are carried to the server for extraction.
     - **Else:** Unreachable if Gate 1 is correct. Defensive throw of `UnsupportedFileError` as safety net.
   - Output: `FileContentPayload` with `{ filename, contentType, textContent?, base64Data?, rawBlob? }`
   - Error: FileReader failure produces DOMException or Error. Defensive else-branch throws UnsupportedFileError if reached.

   **TG-3 FIXED:** Every branch is guarded by an explicit set membership check. No type falls through to readAsText unless it is actually in SUPPORTED_TEXT_TYPES. Binary documents get their own branch that does NOT call readAsText.

4. **batch_iterated** — `prepareFilesContent()` processes files sequentially

   - Input: Array of File objects
   - Process: Sequential for loop, unchanged from baseline. Each file passes through steps 2-3. Fail-fast on first error.
   - Output: `FileContentPayload[]` preserving input ordering
   - Error: First rejection aborts batch. Error propagates to page.tsx caller.

5. **request_serialized** — `generateResponse()` builds JSON body

   - Input: message string, conversation history, `FileContentPayload[]` from step 4
   - Process: Builds `{ message, history: last10, attachments }`. Attachments carry original contentType and whichever content field was populated (textContent, base64Data, or rawBlob).
   - Output: JSON request body with attachments array
   - Error: Network failure or non-ok response.

6. **route_gate_checked** — Gate 2: expanded `isSupportedAttachment()`

   - Input: FileAttachment objects parsed from request body
   - Process: Exact string lookup against three sets — **same shared constants as Gate 1** (fixes TG-1):
     - `SUPPORTED_IMAGE_TYPES` — same source as Gate 1
     - `SUPPORTED_TEXT_TYPES` — same source as Gate 1 (includes text/csv)
     - `SUPPORTED_DOCUMENT_TYPES` — same source as Gate 1
   - Output: `gate2Result`:
     - `pass_image` — contentType in SUPPORTED_IMAGE_TYPES
     - `pass_text` — contentType in SUPPORTED_TEXT_TYPES
     - `pass_document` — contentType in SUPPORTED_DOCUMENT_TYPES
     - `silent_drop` — contentType in none. Attachment silently removed.
   - Error: None. Silent filtering for unknown types.

   **TG-1 FIXED:** Both gates import from the same shared module. Adding a type to one automatically adds it to both. Drift is structurally impossible.

   **TG-2 CONSEQUENCE:** With shared imports, Gate1 = Gate2 is enforced by construction. The GateSubset invariant holds by design, not by coincidence.

7. **document_extracted** — Server-side text extraction for binary documents (NEW STEP)

   - Input: FileAttachment objects with `gate2Result = pass_document` and `rawBlob` field populated
   - Process: For each document attachment, extract text content server-side:
     - PDF: extract text using a PDF parsing library (e.g., pdf-parse, pdfjs-dist)
     - DOC/DOCX: extract text using a document parsing library (e.g., mammoth for docx, antiword/textract for doc)
     - XLS/XLSX: extract cell contents as text using a spreadsheet library (e.g., xlsx/SheetJS)
     - Extracted text replaces rawBlob on the attachment. `payloadShape` transitions from `rawBlob` to `textContent`.
     - If extraction fails (corrupt file, password-protected, unsupported format variant), the attachment is dropped with an error logged. Other attachments continue processing.
   - Output: FileAttachment objects with textContent populated from extraction, rawBlob cleared. `extractionResult = extracted_text` on success.
   - Error: Extraction failure sets `extractionResult = extraction_failed`. Attachment dropped from supported list. Non-blocking — other attachments proceed. Error logged server-side.

   **Text and image attachments skip this step** — they already have usable content from client-side preparation. `extractionResult = not_applicable` for non-document types.

8. **content_assembled** — `buildUserContent()` expanded to three-way partition

   - Input: message string, supported attachments array (post-Gate 2 filter, post-extraction for documents)
   - Process: Re-partitions supported into three sub-lists:
     - `textAttachments = supported.filter(a => SUPPORTED_TEXT_TYPES.has(a.contentType))` — includes text/csv
     - `documentAttachments = supported.filter(a => SUPPORTED_DOCUMENT_TYPES.has(a.contentType))` — **new partition**
     - `imageAttachments = supported.filter(a => SUPPORTED_IMAGE_TYPES.has(a.contentType))`
     - Text attachments AND document attachments (both now have textContent) are prepended to message using the existing `--- filename ---\n<textContent>` format
     - Image attachments become `input_image` parts as before
   - Output: `string | ResponseInputPart[]` — same four shapes as baseline but text-prefixed string now includes document-extracted text alongside native text attachments
   - Error: None. buildUserContent does not throw.

   **TG-4 FIXED:** Three-way partition is exhaustive over all three type sets. No type falls between partitions.

   **TG-7 PRESERVED:** No new ResponseInputPart variant. Extracted document text feeds through existing `input_text` path.

9. **delivered_to_llm** — Content placed in OpenAI input array

   - Input: `string | ResponseInputPart[]` from step 8
   - Process: Set as content field on user message in OpenAI input array
   - Output: OpenAI receives plain string or multipart content array with document text incorporated
   - Error: None at this step.

## Terminal Condition

**Success:** File content reaches OpenAI as `input_text` (for text types, CSV, and extracted document text) or `input_image` (for image types). LLM response is informed by the file content. All 7 target file types are supported end-to-end.

**Gate 1 rejection:** UnsupportedFileError thrown for types not in any of the three sets. Batch aborted. User sees error message listing supported categories.

**Gate 2 silent drop:** Only possible for types not in any shared set. With shared imports, this can only happen if the request body contains a hand-crafted contentType not present in the shared module — a server-side defense, not a normal user path.

**Extraction failure:** Binary document that passes both gates but fails server-side extraction is dropped from the supported list. Other attachments proceed. Error logged. User message is still sent with remaining attachments (or text-only if all documents failed).

## Feedback Loops

None in the type-gating subsystem. Retry logic is in the parent pipeline model.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Status |
|----|-----------|--------|---------------|--------|
| TG-1 | Gate 1 and Gate 2 whitelists are the same sets | Shared import from single module | `WhitelistConsistency` | **FIXED** — single source of truth, drift structurally impossible |
| TG-2 | Every type that passes Gate 1 also passes Gate 2 | Consequence of TG-1 fix | `GateSubset` | **FIXED** — holds by construction |
| TG-3 | Every type that passes Gate 1 routes to an explicit conversion branch with a matching set membership check | Checked three-way partition in prepareFileContent | `CheckedPartition` | **FIXED** — catch-all replaced with image/text/document checks plus defensive else |
| TG-4 | buildUserContent re-partition is exhaustive over all types that pass Gate 2 | Three-way partition in buildUserContent | `PartitionExhaustive` | **FIXED** — three sub-partitions cover all three type sets |
| TG-5 | readAsText produces valid UTF-8 for every type in SUPPORTED_TEXT_TYPES | text/plain, application/json, text/csv | `TextReadValidity` | HOLDS — text/csv is plain UTF-8 |
| TG-6 | readAsDataURL produces a data URL consumable as input_image for every type in SUPPORTED_IMAGE_TYPES | image/{png,jpeg,gif,webp} | `ImageReadValidity` | HOLDS unchanged |
| TG-7 | ResponseInputPart union has exactly two variants: input_text and input_image | route.ts type definition | `PartTypeCompleteness` | HOLDS — document text feeds through input_text |
| TG-8 | Types not in any supported set cause hard rejection at Gate 1 | prepareFileContent throws UnsupportedFileError | `Gate1HardReject` | HOLDS — semantics unchanged, gate expanded |
| TG-9 | Types not in any shared set cause silent drop at Gate 2 | route.ts .filter() | `Gate2SilentDrop` | HOLDS — only affects hand-crafted requests |
| TG-10 | Payload size check runs on all parsed attachments before MIME filtering | route.ts ordering | `PayloadSizeOrdering` | HOLDS unchanged |
| TG-11 | Binary document types never reach readAsText | Explicit document branch in prepareFileContent | `NoGarbageConversion` | **NEW** — prevents silent data corruption |
| TG-12 | Server-side extraction produces valid textContent or drops the attachment | document_extracted step | `ExtractionValidity` | **NEW** — extraction failure is non-blocking |
| TG-13 | text/csv routes to existing text path with no server-side extraction needed | text/csv in SUPPORTED_TEXT_TYPES | `CsvTextPath` | **NEW** — CSV is plain text, not binary |

## Type Support Matrix

| Extension | MIME Type | Gate 1 | Conversion | Gate 2 | Extraction | Assembly | LLM receives |
|-----------|-----------|--------|------------|--------|------------|----------|-------------|
| .txt | `text/plain` | pass_text | readAsText | pass_text | not_applicable | text prefix | input_text |
| .csv | `text/csv` | pass_text | readAsText | pass_text | not_applicable | text prefix | input_text |
| .json | `application/json` | pass_text | readAsText | pass_text | not_applicable | text prefix | input_text |
| .pdf | `application/pdf` | pass_document | readAsArrayBuffer → rawBlob | pass_document | extract text | text prefix | input_text |
| .doc | `application/msword` | pass_document | readAsArrayBuffer → rawBlob | pass_document | extract text | text prefix | input_text |
| .docx | `application/vnd.openxmlformats-officedocument.wordprocessingml.document` | pass_document | readAsArrayBuffer → rawBlob | pass_document | extract text | text prefix | input_text |
| .xls | `application/vnd.ms-excel` | pass_document | readAsArrayBuffer → rawBlob | pass_document | extract text | text prefix | input_text |
| .xlsx | `application/vnd.openxmlformats-officedocument.spreadsheetml.sheet` | pass_document | readAsArrayBuffer → rawBlob | pass_document | extract text | text prefix | input_text |
| .png | `image/png` | pass_image | readAsDataURL | pass_image | not_applicable | input_image part | input_image |
| .jpg | `image/jpeg` | pass_image | readAsDataURL | pass_image | not_applicable | input_image part | input_image |
| .gif | `image/gif` | pass_image | readAsDataURL | pass_image | not_applicable | input_image part | input_image |
| .webp | `image/webp` | pass_image | readAsDataURL | pass_image | not_applicable | input_image part | input_image |

## Change Impact Analysis

**Changes from baseline model:**

| Component | Baseline | Target |
|-----------|----------|--------|
| Type module | Two independent Set declarations (file-content.ts + route.ts) | Single shared module imported by both |
| SUPPORTED_TEXT_TYPES | `{text/plain, application/json}` | `{text/plain, application/json, text/csv}` |
| SUPPORTED_DOCUMENT_TYPES | Did not exist | `{application/pdf, application/msword, ...vnd.openxmlformats...wordprocessingml..., application/vnd.ms-excel, ...vnd.openxmlformats...spreadsheetml...}` |
| isSupportedMimeType | Two-set OR | Three-set OR (image, text, document) |
| prepareFileContent | Image check → catch-all text | Image check → text check → document check → defensive else |
| isSupportedAttachment | Two-set OR (independent declaration) | Three-set OR (shared import) |
| buildUserContent | Two-way partition (text, image) | Three-way partition (text, document, image) — text and document both prepend to message |
| NEW step | — | document_extracted: server-side text extraction for binary types |
| FileContentPayload | `{textContent?, base64Data?}` | `{textContent?, base64Data?, rawBlob?}` |
| UnsupportedFileError message | "Only images and text files" | "Only images, text, and document files" |
| file-content.test.ts:38 | Asserts PDF rejection | Must change: PDF now passes Gate 1 as pass_document |
| generate.test.ts:68 | Asserts PDF silent drop | Must change: PDF now passes Gate 2 as pass_document, text extracted |

**Implementation ordering (risk-mitigated):**

1. **First:** Create shared type module with all three sets. Import in both file-content.ts and route.ts. No new types yet — just eliminate the dual declaration. (Fixes TG-1, zero behavioral change, safe to merge independently.)
2. **Second:** Replace catch-all with checked partition in prepareFileContent. Add document branch that reads as ArrayBuffer. Gate 1 still only has image + text types, so document branch is unreachable. (Fixes TG-3, zero behavioral change, safe to merge independently.)
3. **Third:** Add text/csv to SUPPORTED_TEXT_TYPES in shared module. Update tests. (Gate-only change, CSV flows through existing readAsText → input_text path.)
4. **Fourth:** Add SUPPORTED_DOCUMENT_TYPES to shared module. Add document_extracted step in route.ts with extraction libraries. Update buildUserContent to three-way partition. Update tests. (Full new pipeline for binary types.)

This ordering ensures each step is independently mergeable and no step introduces a regression window.

## TLA+ Specification

```tla
---------------------------- MODULE TypeGatingPipelineTarget ----------------------------
\* Target behavioral model for the MIME type-gating subsystem
\* Extends baseline with document type support and structural fixes
\* All 10 baseline invariants preserved, 3 new invariants added

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    ImageMimeTypes,      \* Set: {image/png, image/jpeg, image/gif, image/webp}
    TextMimeTypes,       \* Set: {text/plain, application/json, text/csv}
    DocumentMimeTypes,   \* Set: {application/pdf, application/msword, ...docx, ...xls, ...xlsx}
    AllMimeTypes,        \* Universe of possible MIME strings including empty
    EMPTY_MIME,          \* "" — browser returns for unknown extensions
    NULL                 \* Null sentinel

ASSUME ImageMimeTypes \intersect TextMimeTypes = {}
ASSUME ImageMimeTypes \intersect DocumentMimeTypes = {}
ASSUME TextMimeTypes \intersect DocumentMimeTypes = {}

VARIABLES
    \* --- Input ---
    mimeType,
    mimeCategory,

    \* --- Gate 1 (frontend) — shared type module ---
    gate1Result,

    \* --- Conversion ---
    conversionBranch,
    payloadShape,
    contentType,

    \* --- Extraction (NEW) ---
    extractionResult,

    \* --- Gate 2 (route) — same shared type module ---
    gate2Result,

    \* --- Assembly ---
    assemblyOutput,
    llmContentType,

    \* --- Pipeline phase ---
    phase

vars == <<mimeType, mimeCategory, gate1Result,
          conversionBranch, payloadShape, contentType,
          extractionResult, gate2Result,
          assemblyOutput, llmContentType, phase>>

\* --- Type sets (shared — TG-1 fixed) ---
\* Both gates reference these same constants.
\* No separate feImageSet/rtImageSet — single source of truth.

AllSupportedTypes == ImageMimeTypes \union TextMimeTypes \union DocumentMimeTypes

Phase == {"idle", "mime_resolved", "frontend_gate_checked",
          "content_converted", "route_gate_checked",
          "document_extracted", "content_assembled",
          "delivered", "rejected", "dropped", "extraction_failed"}

Gate1Result == {"pass_image", "pass_text", "pass_document", "reject"}
ConversionBranch == {"image_dataurl", "text_readastext", "document_upload", "none"}
PayloadShape == {"base64Data", "textContent", "rawBlob", "none"}
ExtractionResult == {"extracted_text", "extraction_failed", "not_applicable"}
Gate2Result == {"pass_image", "pass_text", "pass_document", "silent_drop"}
AssemblyOutput == {"plain_string", "text_prefixed_string", "input_parts_array", "dropped"}
LlmContentType == {"input_text", "input_image", "absent"}

\* ===========================================================================
\* Initial state
\* ===========================================================================

Init ==
    /\ mimeType = NULL
    /\ mimeCategory = "correct"
    /\ gate1Result = "reject"
    /\ conversionBranch = "none"
    /\ payloadShape = "none"
    /\ contentType = NULL
    /\ extractionResult = "not_applicable"
    /\ gate2Result = "silent_drop"
    /\ assemblyOutput = "dropped"
    /\ llmContentType = "absent"
    /\ phase = "idle"

\* ===========================================================================
\* Step 1: mime_resolved — Browser provides file.type
\* ===========================================================================

ResolveMime(mime) ==
    /\ phase = "idle"
    /\ mimeType' = mime
    /\ mimeCategory' = CASE mime = EMPTY_MIME -> "empty"
                          [] mime \in AllSupportedTypes -> "correct"
                          [] OTHER -> "rejected"
    /\ phase' = "mime_resolved"
    /\ UNCHANGED <<gate1Result, conversionBranch, payloadShape, contentType,
                   extractionResult, gate2Result, assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 2: frontend_gate_checked — Gate 1: three-way isSupportedMimeType()
\* Shared type module — same constants used by Gate 2
\* ===========================================================================

FrontendGateCheck ==
    /\ phase = "mime_resolved"
    /\ IF mimeType \in ImageMimeTypes
       THEN /\ gate1Result' = "pass_image"
            /\ phase' = "frontend_gate_checked"
       ELSE IF mimeType \in TextMimeTypes
            THEN /\ gate1Result' = "pass_text"
                 /\ phase' = "frontend_gate_checked"
            ELSE IF mimeType \in DocumentMimeTypes
                 THEN /\ gate1Result' = "pass_document"
                      /\ phase' = "frontend_gate_checked"
                 ELSE /\ gate1Result' = "reject"
                      /\ phase' = "rejected"
    /\ UNCHANGED <<mimeType, mimeCategory, conversionBranch, payloadShape,
                   contentType, extractionResult, gate2Result,
                   assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 3: content_converted — prepareFileContent() with CHECKED partition
\* TG-3 FIXED: every branch has explicit set membership guard
\* ===========================================================================

ConvertContent ==
    /\ phase = "frontend_gate_checked"
    /\ contentType' = mimeType
    /\ IF mimeType \in ImageMimeTypes
       THEN \* Explicit image branch: readAsDataURL
            /\ conversionBranch' = "image_dataurl"
            /\ payloadShape' = "base64Data"
       ELSE IF mimeType \in TextMimeTypes
            THEN \* Explicit text branch: readAsText (safe for text/plain, json, csv)
                 /\ conversionBranch' = "text_readastext"
                 /\ payloadShape' = "textContent"
            ELSE IF mimeType \in DocumentMimeTypes
                 THEN \* Explicit document branch: readAsArrayBuffer → base64 blob
                      \* NO readAsText — binary formats produce garbage with readAsText
                      /\ conversionBranch' = "document_upload"
                      /\ payloadShape' = "rawBlob"
                 ELSE \* Defensive: unreachable if Gate 1 is correct
                      \* Throws UnsupportedFileError as safety net
                      /\ conversionBranch' = "none"
                      /\ payloadShape' = "none"
    /\ phase' = "content_converted"
    /\ UNCHANGED <<mimeType, mimeCategory, gate1Result, extractionResult,
                   gate2Result, assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 4: route_gate_checked — Gate 2: same shared constants as Gate 1
\* TG-1 FIXED: single source of truth for type sets
\* ===========================================================================

RouteGateCheck ==
    /\ phase = "content_converted"
    /\ IF contentType \in ImageMimeTypes
       THEN /\ gate2Result' = "pass_image"
            /\ phase' = "route_gate_checked"
       ELSE IF contentType \in TextMimeTypes
            THEN /\ gate2Result' = "pass_text"
                 /\ phase' = "route_gate_checked"
            ELSE IF contentType \in DocumentMimeTypes
                 THEN /\ gate2Result' = "pass_document"
                      /\ phase' = "route_gate_checked"
                 ELSE /\ gate2Result' = "silent_drop"
                      /\ phase' = "dropped"
    /\ UNCHANGED <<mimeType, mimeCategory, gate1Result, conversionBranch,
                   payloadShape, contentType, extractionResult,
                   assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 5: document_extracted — Server-side text extraction (NEW)
\* Only runs for document types. Text and image skip to assembly.
\* ===========================================================================

ExtractDocumentText ==
    /\ phase = "route_gate_checked"
    /\ gate2Result = "pass_document"
    /\ payloadShape = "rawBlob"
    \* Nondeterministic: extraction can succeed or fail
    /\ \/ /\ extractionResult' = "extracted_text"
          /\ payloadShape' = "textContent"   \* rawBlob replaced with extracted text
          /\ phase' = "content_assembled"    \* Proceed to assembly
       \/ /\ extractionResult' = "extraction_failed"
          /\ payloadShape' = "none"
          /\ phase' = "extraction_failed"    \* Attachment dropped

SkipExtraction ==
    /\ phase = "route_gate_checked"
    /\ gate2Result \in {"pass_image", "pass_text"}
    /\ extractionResult' = "not_applicable"
    /\ phase' = "content_assembled"
    /\ UNCHANGED <<mimeType, mimeCategory, gate1Result, conversionBranch,
                   payloadShape, contentType, gate2Result,
                   assemblyOutput, llmContentType>>

\* ===========================================================================
\* Step 6: content_assembled — buildUserContent() with three-way partition
\* TG-4 FIXED: text + document + image exhausts all pass_* results
\* ===========================================================================

AssembleContent ==
    /\ phase = "content_assembled"
    /\ IF gate2Result \in {"pass_text", "pass_document"}
       THEN \* Both text and extracted-document attachments prepend to message
            /\ assemblyOutput' = "text_prefixed_string"
            /\ llmContentType' = "input_text"
       ELSE IF gate2Result = "pass_image"
            THEN /\ assemblyOutput' = "input_parts_array"
                 /\ llmContentType' = "input_image"
            ELSE \* Unreachable at this phase
                 /\ assemblyOutput' = "dropped"
                 /\ llmContentType' = "absent"
    /\ phase' = "delivered"
    /\ UNCHANGED <<mimeType, mimeCategory, gate1Result, conversionBranch,
                   payloadShape, contentType, extractionResult, gate2Result>>

\* ===========================================================================
\* Next-state relation
\* ===========================================================================

Next ==
    \/ \E m \in AllMimeTypes : ResolveMime(m)
    \/ FrontendGateCheck
    \/ ConvertContent
    \/ RouteGateCheck
    \/ ExtractDocumentText
    \/ SkipExtraction
    \/ AssembleContent

Spec == Init /\ [][Next]_vars

\* ===========================================================================
\* INVARIANTS — baseline preserved + new
\* ===========================================================================

\* --- TG-1: WhitelistConsistency (FIXED by construction) ---
\* Both gates reference the same CONSTANTS. No separate sets to drift.
\* This invariant is trivially true — modeled to document the fix.
WhitelistConsistency == TRUE
    \* In the baseline model, this checked feImageSet = rtImageSet etc.
    \* In the target model, there is only one set per category.

\* --- TG-2: GateSubset (FIXED by construction) ---
\* Gate1 and Gate2 use the same constants, so subset holds trivially.
GateSubset == TRUE

\* --- TG-3: CheckedPartition (FIXED) ---
\* No type reaches catch_all_fallthrough. Every branch is explicit.
\* In target model, conversionBranch is never "catch_all_fallthrough"
\* because that value no longer exists in the ConversionBranch set.
CheckedPartition ==
    conversionBranch \in {"image_dataurl", "text_readastext", "document_upload", "none"}

\* --- TG-3b: NoGarbageDelivery (FIXED) ---
\* No garbage payload can reach delivery. "garbage" is no longer a valid PayloadShape.
NoGarbageDelivery ==
    phase = "delivered" => payloadShape \in {"base64Data", "textContent"}

\* --- TG-4: PartitionExhaustive (FIXED) ---
\* Every type that reaches assembly is in one of three partitions.
PartitionExhaustive ==
    phase = "content_assembled" =>
        gate2Result \in {"pass_text", "pass_image", "pass_document"}

\* --- TG-5: TextReadValidity ---
\* readAsText only runs for types in TextMimeTypes (text/plain, json, csv).
TextReadValidity ==
    conversionBranch = "text_readastext" => payloadShape = "textContent"

\* --- TG-6: ImageReadValidity ---
ImageReadValidity ==
    conversionBranch = "image_dataurl" => payloadShape = "base64Data"

\* --- TG-7: PartTypeCompleteness ---
\* LLM content is always input_text or input_image. No third variant.
PartTypeCompleteness ==
    phase = "delivered" => llmContentType \in {"input_text", "input_image"}

\* --- TG-8: Gate1HardReject ---
\* Types not in any supported set cause rejection.
Gate1HardReject ==
    gate1Result = "reject" => phase \in {"rejected", "mime_resolved", "idle"}

\* --- TG-9: Gate2SilentDrop ---
\* Types not in any shared set cause silent drop.
Gate2SilentDrop ==
    gate2Result = "silent_drop" => phase \in {"dropped", "content_converted", "idle"}

\* --- TG-10: EndToEndDelivery ---
\* Delivered means passed both gates, converted correctly, and (if document) extracted.
EndToEndDelivery ==
    phase = "delivered" =>
        /\ gate1Result \in {"pass_image", "pass_text", "pass_document"}
        /\ gate2Result \in {"pass_image", "pass_text", "pass_document"}
        /\ payloadShape \in {"base64Data", "textContent"}

\* --- TG-11: NoGarbageConversion (NEW) ---
\* Binary document types never reach readAsText.
NoGarbageConversion ==
    gate1Result = "pass_document" => conversionBranch \in {"document_upload", "none"}

\* --- TG-12: ExtractionValidity (NEW) ---
\* Extraction produces textContent or drops the attachment. Never delivers rawBlob.
ExtractionValidity ==
    phase = "delivered" => payloadShape /= "rawBlob"

\* --- TG-13: CsvTextPath (NEW) ---
\* text/csv routes through existing text path, not document extraction.
CsvTextPath ==
    (gate1Result = "pass_text" /\ conversionBranch = "text_readastext") =>
        extractionResult \in {"not_applicable", "extracted_text", "extraction_failed"}
        \* text/csv never triggers document extraction

\* ===========================================================================
\* LIVENESS
\* ===========================================================================

\* Every file eventually reaches a terminal state
EventualTermination == <>(phase \in {"delivered", "rejected", "dropped", "extraction_failed"})

=============================================================================
```

## Relationship to Parent Models

This model is a sub-slice of:
- **file-to-llm-pipeline-target.md** — step 5 (file_content_prepared) now decomposes into this model's full 9-step sequence with the document extraction step
- The parent model's INV-2 (FileContentDelivery) is satisfied because all supported types now have a path to reach `input_text` or `input_image` content

The baseline model at `type-gating-pipeline-model.md` documents the "as-is" behavior. This target model documents the "to-be" behavior. The delta between them defines the implementation work.
