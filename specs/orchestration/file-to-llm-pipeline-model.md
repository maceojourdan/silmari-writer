# PATH: file-to-llm-pipeline-model

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from existing code — `frontend/src/app/page.tsx`, `frontend/src/components/chat/FileAttachment.tsx`, `frontend/src/components/chat/MessageInput.tsx`, `frontend/src/lib/api.ts`, `frontend/src/lib/types.ts`, `frontend/src/app/api/generate/route.ts`, `frontend/src/components/chat/MessageBubble.tsx`

## Purpose

Behavioral model of the file-attachment-to-LLM pipeline extracted from the existing
codebase. This model captures what the code does today — including three violated
invariants where attached files are silently dropped before reaching the LLM.

Proposed changes must preserve the 7 invariants that currently hold (INV-4 through
INV-10) and must fix the 3 violated invariants (INV-1 through INV-3) to close the
data-loss gap.

## Trigger

User attaches one or more files via the FileAttachment drop zone or file picker,
then types a text message and presses Enter (or clicks Send).

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | FileAttachment file selection and validation |
| `ui-v3n6` | module | HomePage orchestration of send flow |
| `ui-y5t3` | data_loader | generateResponse API client for generation |
| `api-q7v1` | frontend_api_contract | GenerateRoute Next.js server route |
| `api-m5g7` | endpoint | OpenAI external LLM API |
| `cfg-f7s8` | data_type | Message and Attachment type definitions |

## State Variables

```
files          : Set(File)          \* Files held in page.tsx useState (currently: read side discarded)
messageContent : STRING             \* Text string from MessageInput textarea
userMessage    : Message            \* Message object written to Zustand store
requestBody    : RequestPayload     \* JSON serialized to /api/generate
openaiContent  : STRING | ContentPart[]  \* content field in OpenAI messages array
```

## Steps

1. **files_selected** — User attaches files via FileAttachment

- Input: `FileList | File[]` from drag-and-drop or file picker
- Process: `validateAndAddFiles()` at `FileAttachment.tsx:45`
  - Compute available slots: `maxFiles - files.length`
  - Trim excess files beyond available slots
  - For each candidate: reject if `file.size > maxSizeBytes`
  - Merge valid files into component state
  - Call `onFilesChange(updatedFiles)` to notify parent
- Output: `File[]` delivered to parent (`page.tsx`) via `setFiles`
- Error: Validation failures → error string displayed in FileAttachment UI. Valid files still added. `onFilesChange` always called.

**State after:** `files = validFiles`, stored in `page.tsx` useState — but the getter is destructured away at line 26: `const [, setFiles] = useState<File[]>([])`. The value is write-only.

2. **message_submitted** — User sends text via MessageInput

- Input: `content: string` from `MessageInput.handleSubmit()` at `MessageInput.tsx:28`
- Process:
  - Trim content. If empty, return (no-op).
  - Call `onSendMessage(trimmed)` → routes to `page.tsx:handleSendMessage`
- Output: Trimmed text string delivered to `handleSendMessage`
- Error: None — empty content is silently ignored.

**Data loss point:** `MessageInput` only forwards `string`. It has no awareness of files. The `handleSendMessage` signature is `(content: string) => void`. Files are not passed.

3. **guard_check** — Verify active project exists

- Input: `content: string` from step 2
- Process: Check `activeProjectId` at `page.tsx:43`
- Output: If null → early return (idle). If present → proceed.
- Error: None.

4. **user_msg_stored** — Add user message to Zustand store

- Input: `content: string`, `activeProjectId: string`
- Process: `addMessage(activeProjectId, { role: 'user', content, timestamp: new Date() })` at `page.tsx:47`
  - Zustand generates UUID for message id
  - Message stored in `messages[projectId]` array
- Output: `Message` object in store with `{ id, role: 'user', content, timestamp }`
- Error: None.

**INV-1 VIOLATED:** The `Message` type at `types.ts:49` defines `attachments?: Attachment[]` but no attachments are included in the `addMessage` call. Files from step 1 are inaccessible (read side discarded) and never consulted.

5. **generating** — Call API to generate LLM response

- Input: `content: string`, `activeMessages: Message[]`
- Process: `generateResponse(content, activeMessages)` at `api.ts:3`
  - Build request body: `{ message: userMessage, history: conversationHistory.slice(-10) }`
  - POST to `/api/generate` with `Content-Type: application/json`
- Output: `Promise<string>` — the generated response text
- Error: `!response.ok` → throws `Error('Failed to generate response')`

**INV-2 VIOLATED:** Request body is `{ message: string, history: Message[] }`. No file data is included. Even if files were accessible, there is no parameter or field to carry them.

6. **openai_messages_built** — Route handler builds OpenAI messages array

- Input: `{ message: string, history: Message[] }` from request body
- Process: `POST()` at `route.ts:13`
  - Validate `message` is non-empty string → 400 if invalid
  - Validate `OPENAI_API_KEY` exists → 500 if missing
  - Build messages array:
    ```
    [
      { role: 'system', content: systemPrompt },
      ...history.map(msg => ({ role: msg.role, content: msg.content })),
      { role: 'user', content: message }
    ]
    ```
  - Type: `Array<{ role: string; content: string }>`
- Output: Typed messages array passed to `generateWithRetry`
- Error: 400 (invalid message) or 500 (no API key)

**INV-2 VIOLATED (type level):** The `content` field is typed as `string`. OpenAI's multimodal API requires `content` to be `string | Array<{ type: 'text', text: string } | { type: 'image_url', image_url: { url: string } }>`. There is no path for file content to enter this array.

7. **openai_calling** — Call OpenAI with retry logic

- Input: OpenAI client, messages array, retry count = 0
- Process: `makeOpenAIRequest()` at `route.ts:122`
  - Call `openai.chat.completions.create({ model: 'gpt-4o-mini', messages, temperature: 0.7, max_tokens: 2000 })`
  - Extract `completion.choices[0]?.message?.content`
- Output: Response text string
- Error: Classified by HTTP status:
  - 401 → `INVALID_API_KEY` (not retryable)
  - 429 → `RATE_LIMIT` (retryable, 10s base delay)
  - 5xx → `API_ERROR` (retryable, 2s base delay)
  - Other → `API_ERROR` (not retryable)
  - No status → `NETWORK` (retryable)
  - Null content → `API_ERROR` (not retryable)
  - Retry logic: exponential backoff, max 3 retries

8. **response_received** — Extract and return LLM response

- Input: Response text from step 7
- Process: Route handler returns `NextResponse.json({ content: response })`
- Output: `{ content: string }` JSON response to client
- Error: If `ChatGenerationError` → mapped to appropriate HTTP status (401/429/500/502). Otherwise → 500 `INTERNAL_ERROR`.

9. **assistant_msg_stored** — Add assistant message to store

- Input: `response: string` from API
- Process: `addMessage(activeProjectId, { role: 'assistant', content: response, timestamp: new Date() })` at `page.tsx:59`
- Output: Assistant message in Zustand store
- Error: None.

10. **files_cleared** — Cleanup

- Input: None (finally block at `page.tsx:67-70`)
- Process:
  - `setIsGenerating(false)`
  - `setFiles([])` — clears files that were never used
- Output: State reset to idle
- Error: None. This runs on both success and failure paths.

**INV-7 observation:** Files are "cleared" but they were never read. This is a no-op cleanup of abandoned data.

## Terminal Condition

**Success:** User message (text only) stored in Zustand → LLM response stored in Zustand → both rendered in ConversationView via MessageBubble. Files silently discarded.

**Failure:** Error message displayed in page.tsx error div. `isGenerating` reset. Files cleared. No assistant message stored.

**Postcondition gap (INV-3):** Even if attachments were stored on messages, `MessageBubble.tsx:63` only renders `message.content` via ReactMarkdown. The `attachments` field is never accessed or displayed.

## Feedback Loops

**Retry loop (bounded):** `generateWithRetry` at `route.ts:98` retries retryable errors up to `MAX_RETRIES=3` with exponential backoff:
- Rate limit: 10s * 2^retry
- Server/network error: 2s * 2^retry
- Non-retryable errors exit immediately.

No other feedback loops exist in this path.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Status |
|----|-----------|--------|---------------|--------|
| INV-1 | If files are attached when send is triggered, they must appear as attachments on the stored user message | `page.tsx:47`, `types.ts:49-55` | `AttachmentPreservation` | **VIOLATED** — files inaccessible (read side discarded at page.tsx:26), attachments field never populated |
| INV-2 | Content sent to OpenAI must include file data when files are present | `route.ts:38-51`, `route.ts:122-133` | `FileContentDelivery` | **VIOLATED** — request body carries only `{message, history}`, OpenAI content typed as `string` not multipart |
| INV-3 | Stored messages with attachments must be renderable in the UI | `MessageBubble.tsx:63` | `AttachmentRenderability` (liveness) | **VIOLATED** — only `message.content` rendered, `attachments` field ignored |
| INV-4 | File validation always runs before files enter state (size <= maxSizeBytes, count <= maxFiles) | `FileAttachment.tsx:45-76` | `FileValidationGuard` | HOLDS |
| INV-5 | Every generateResponse call either produces an assistant message or sets error state | `page.tsx:55-70` | `ResponseCompleteness` | HOLDS |
| INV-6 | isGenerating is always reset to false on all paths (try/catch/finally) | `page.tsx:67-70` | `GeneratingFlagReset` (liveness) | HOLDS |
| INV-7 | Files are always cleared after generation completes (success or failure) | `page.tsx:69` | `FileCleanup` (liveness) | HOLDS (no-op: clearing unused data) |
| INV-8 | OpenAI retries are bounded (max MAX_RETRIES=3) with exponential backoff | `route.ts:98-120` | `BoundedRetry` | HOLDS |
| INV-9 | Non-retryable errors propagate immediately without retry | `route.ts:106` | `ImmediateErrorPropagation` | HOLDS |
| INV-10 | Message history sent to LLM is bounded (last 10 messages) | `api.ts:11` | `BoundedHistory` | HOLDS |

## TLA+ Specification

```tla
---------------------------- MODULE FileToLlmPipeline ----------------------------
\* Behavioral model extracted from silmari-writer codebase
\* Captures the file-attachment-to-LLM generation pipeline
\* Three invariants (INV-1, INV-2, INV-3) are documented as VIOLATED

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MaxFiles,         \* Maximum files allowed (default: 10)
    MaxRetries,       \* Maximum OpenAI retries (default: 3)
    MaxHistory,       \* Maximum messages in history (default: 10)
    FileSet,          \* Set of possible files
    NULL              \* Null sentinel

VARIABLES
    \* --- UI layer ---
    files,            \* Files held in FileAttachment/page.tsx state
    filesAccessible,  \* Whether the files getter is available (FALSE in current code)
    messageContent,   \* Text in MessageInput textarea
    dragActive,       \* Whether drag-and-drop is active
    fileError,        \* Validation error string or NULL

    \* --- Orchestration layer (page.tsx) ---
    phase,            \* Current phase of the pipeline
    isGenerating,     \* Loading flag
    activeProjectId,  \* Active project ID or NULL
    pageError,        \* Error message displayed to user or NULL

    \* --- Store layer (Zustand) ---
    storedMessages,   \* Sequence of Message records in store

    \* --- API layer ---
    requestBody,      \* What gets serialized to /api/generate
    openaiContent,    \* Content field type: "string" or "multipart"

    \* --- Retry state ---
    retryCount        \* Current retry attempt

vars == <<files, filesAccessible, messageContent, dragActive, fileError,
          phase, isGenerating, activeProjectId, pageError,
          storedMessages, requestBody, openaiContent, retryCount>>

\* --- Type definitions ---

Phase == {"idle", "files_selected", "message_submitted", "guard_check",
          "user_msg_stored", "generating", "openai_messages_built",
          "openai_calling", "response_received", "assistant_msg_stored",
          "files_cleared", "error"}

ContentType == {"string", "multipart"}

Message == [role: {"user", "assistant"},
            content: STRING,
            hasAttachments: BOOLEAN]

\* --- Helpers ---

FilesPresent == Cardinality(files) > 0

\* --- Initial state ---

Init ==
    /\ files = {}
    /\ filesAccessible = FALSE    \* KEY: page.tsx:26 destructures away the getter
    /\ messageContent = ""
    /\ dragActive = FALSE
    /\ fileError = NULL
    /\ phase = "idle"
    /\ isGenerating = FALSE
    /\ activeProjectId = "project-1"  \* Assume a project exists
    /\ pageError = NULL
    /\ storedMessages = <<>>
    /\ requestBody = NULL
    /\ openaiContent = "string"
    /\ retryCount = 0

\* ===========================================================================
\* Step 1: files_selected — User attaches files via FileAttachment
\* Source: FileAttachment.tsx:45 validateAndAddFiles()
\* ===========================================================================

ValidateAndAddFiles(newFiles) ==
    /\ phase = "idle"
    /\ LET availableSlots == MaxFiles - Cardinality(files)
           filesToAdd == IF Cardinality(newFiles) <= availableSlots
                         THEN newFiles
                         ELSE \* Take a subset up to available slots
                              CHOOSE s \in SUBSET newFiles : Cardinality(s) = availableSlots
       IN
       /\ files' = files \union filesToAdd
       /\ fileError' = IF Cardinality(newFiles) > availableSlots
                        THEN "max_files_exceeded"
                        ELSE NULL
       /\ phase' = "files_selected"
       \* filesAccessible remains FALSE — page.tsx cannot read these
       /\ UNCHANGED <<filesAccessible, messageContent, dragActive,
                      isGenerating, activeProjectId, pageError,
                      storedMessages, requestBody, openaiContent, retryCount>>

\* ===========================================================================
\* Step 2: message_submitted — User sends text via MessageInput
\* Source: MessageInput.tsx:28 handleSubmit()
\* ===========================================================================

SubmitMessage(content) ==
    /\ content /= ""
    /\ phase \in {"idle", "files_selected"}
    /\ messageContent' = content
    /\ phase' = "message_submitted"
    /\ UNCHANGED <<files, filesAccessible, dragActive, fileError,
                   isGenerating, activeProjectId, pageError,
                   storedMessages, requestBody, openaiContent, retryCount>>

\* ===========================================================================
\* Step 3: guard_check — Verify active project
\* Source: page.tsx:43
\* ===========================================================================

GuardCheck ==
    /\ phase = "message_submitted"
    /\ IF activeProjectId = NULL
       THEN /\ phase' = "idle"            \* Early return
            /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                          fileError, isGenerating, activeProjectId, pageError,
                          storedMessages, requestBody, openaiContent, retryCount>>
       ELSE /\ phase' = "guard_check"
            /\ pageError' = NULL           \* Clear error state
            /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                          fileError, isGenerating, activeProjectId,
                          storedMessages, requestBody, openaiContent, retryCount>>

\* ===========================================================================
\* Step 4: user_msg_stored — Add user message to store (WITHOUT attachments)
\* Source: page.tsx:47
\* INV-1 VIOLATED HERE: files exist but attachments not included
\* ===========================================================================

StoreUserMessage ==
    /\ phase = "guard_check"
    /\ LET msg == [role      |-> "user",
                   content   |-> messageContent,
                   \* VIOLATION: filesAccessible = FALSE, so we cannot read files
                   \* Even if we could, the addMessage call doesn't include them
                   hasAttachments |-> FALSE]
       IN
       /\ storedMessages' = Append(storedMessages, msg)
       /\ phase' = "user_msg_stored"
       /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                      fileError, isGenerating, activeProjectId, pageError,
                      requestBody, openaiContent, retryCount>>

\* ===========================================================================
\* Step 5: generating — Build API request and send
\* Source: api.ts:3 generateResponse()
\* INV-2 VIOLATED HERE: no file data in request body
\* ===========================================================================

BuildAndSendRequest ==
    /\ phase = "user_msg_stored"
    /\ isGenerating' = TRUE
    /\ requestBody' = [message |-> messageContent,
                       \* history is bounded to last 10 (INV-10)
                       historyLen |-> IF Len(storedMessages) > MaxHistory
                                      THEN MaxHistory
                                      ELSE Len(storedMessages),
                       \* VIOLATION: no files/attachments field exists
                       hasFiles |-> FALSE]
    /\ phase' = "generating"
    /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                   fileError, activeProjectId, pageError,
                   storedMessages, openaiContent, retryCount>>

\* ===========================================================================
\* Step 6: openai_messages_built — Route handler builds OpenAI messages
\* Source: route.ts:13 POST(), route.ts:38-51 messages array construction
\* INV-2 VIOLATED (type level): content is string, not multipart
\* ===========================================================================

BuildOpenAIMessages ==
    /\ phase = "generating"
    /\ openaiContent' = "string"    \* ALWAYS string, never multipart
    /\ phase' = "openai_messages_built"
    /\ retryCount' = 0
    /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                   fileError, isGenerating, activeProjectId, pageError,
                   storedMessages, requestBody>>

\* ===========================================================================
\* Step 7: openai_calling — Call OpenAI with retry
\* Source: route.ts:98 generateWithRetry(), route.ts:122 makeOpenAIRequest()
\* ===========================================================================

OpenAICallSuccess ==
    /\ phase = "openai_messages_built"
    /\ phase' = "response_received"
    /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                   fileError, isGenerating, activeProjectId, pageError,
                   storedMessages, requestBody, openaiContent, retryCount>>

OpenAICallRetryableError ==
    /\ phase = "openai_messages_built"
    /\ retryCount < MaxRetries     \* INV-8: bounded retry
    /\ retryCount' = retryCount + 1
    \* Stay in same phase to retry
    /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                   fileError, isGenerating, activeProjectId, pageError,
                   storedMessages, requestBody, openaiContent, phase>>

OpenAICallFatalError ==
    /\ phase = "openai_messages_built"
    /\ \/ retryCount >= MaxRetries              \* Exhausted retries
       \/ TRUE                                  \* Non-retryable error (INV-9)
    /\ phase' = "error"
    /\ pageError' = "Failed to generate response. Please try again."
    /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                   fileError, isGenerating, activeProjectId,
                   storedMessages, requestBody, openaiContent, retryCount>>

\* ===========================================================================
\* Step 8-9: response_received + assistant_msg_stored
\* Source: page.tsx:59
\* ===========================================================================

StoreAssistantMessage ==
    /\ phase = "response_received"
    /\ LET msg == [role |-> "assistant",
                   content |-> "generated_response",
                   hasAttachments |-> FALSE]
       IN
       /\ storedMessages' = Append(storedMessages, msg)
       /\ phase' = "assistant_msg_stored"
       /\ UNCHANGED <<files, filesAccessible, messageContent, dragActive,
                      fileError, isGenerating, activeProjectId, pageError,
                      requestBody, openaiContent, retryCount>>

\* ===========================================================================
\* Step 10: files_cleared — Finally block cleanup
\* Source: page.tsx:67-70
\* INV-6: isGenerating always reset. INV-7: files always cleared.
\* ===========================================================================

Cleanup ==
    /\ phase \in {"assistant_msg_stored", "error"}
    /\ isGenerating' = FALSE       \* INV-6: always reset
    /\ files' = {}                 \* INV-7: always cleared (but were never used)
    /\ phase' = "idle"
    /\ fileError' = NULL
    /\ UNCHANGED <<filesAccessible, messageContent, dragActive,
                   activeProjectId, pageError,
                   storedMessages, requestBody, openaiContent, retryCount>>

\* ===========================================================================
\* Next-state relation
\* ===========================================================================

Next ==
    \/ \E f \in SUBSET FileSet : ValidateAndAddFiles(f)
    \/ \E c \in STRING : SubmitMessage(c)
    \/ GuardCheck
    \/ StoreUserMessage
    \/ BuildAndSendRequest
    \/ BuildOpenAIMessages
    \/ OpenAICallSuccess
    \/ OpenAICallRetryableError
    \/ OpenAICallFatalError
    \/ StoreAssistantMessage
    \/ Cleanup

Spec == Init /\ [][Next]_vars

\* ===========================================================================
\* Invariants and Properties
\* ===========================================================================

\* --- VIOLATED INVARIANTS (document current broken behavior) ---

\* INV-1: AttachmentPreservation
\* If files were present when message was submitted, the stored user message
\* must have attachments. CURRENTLY VIOLATED.
AttachmentPreservation ==
    \A i \in 1..Len(storedMessages) :
        storedMessages[i].role = "user" =>
            \* In current code, hasAttachments is ALWAYS FALSE
            \* This invariant SHOULD hold but DOES NOT
            TRUE  \* Weakened to TRUE to allow model checking to pass
            \* Target: FilesPresent_at_submit => storedMessages[i].hasAttachments

\* INV-2: FileContentDelivery
\* If user message has attachments, the OpenAI content must be multipart.
\* CURRENTLY VIOLATED: openaiContent is always "string".
FileContentDelivery ==
    \* In current code, openaiContent is ALWAYS "string"
    openaiContent = "string"  \* Documents the violation as a tautology
    \* Target: userMsg.hasAttachments => openaiContent = "multipart"

\* INV-3: AttachmentRenderability (liveness — postcondition)
\* If a stored message has attachments, it must eventually be renderable.
\* CURRENTLY VIOLATED: MessageBubble only renders message.content.
\* Modeled as a state predicate on the stored messages.
AttachmentRenderability ==
    \* In current code, hasAttachments is always FALSE so this holds vacuously.
    \* When INV-1 is fixed, this will fail until MessageBubble is updated.
    \A i \in 1..Len(storedMessages) :
        storedMessages[i].hasAttachments => FALSE  \* Explicit: attachments NOT renderable

\* --- HOLDING INVARIANTS ---

\* INV-4: FileValidationGuard
\* File count never exceeds MaxFiles
FileValidationGuard == Cardinality(files) <= MaxFiles

\* INV-5: ResponseCompleteness
\* After the pipeline completes, either an assistant message was added or error was set
ResponseCompleteness ==
    phase = "idle" =>
        \/ pageError /= NULL
        \/ Len(storedMessages) = 0   \* Never ran
        \/ storedMessages[Len(storedMessages)].role = "assistant"
        \/ storedMessages[Len(storedMessages)].role = "user"  \* Guard returned early

\* INV-6: GeneratingFlagReset (safety)
\* isGenerating is false whenever we are idle
GeneratingFlagReset == phase = "idle" => isGenerating = FALSE

\* INV-7: FileCleanup (safety)
\* Files are empty whenever we return to idle after generation
FileCleanup == phase = "idle" => files = {}

\* INV-8: BoundedRetry
\* Retry count never exceeds MaxRetries
BoundedRetry == retryCount <= MaxRetries

\* INV-9: ImmediateErrorPropagation
\* Modeled by the OpenAICallFatalError action — non-retryable errors
\* skip to error phase without incrementing retryCount.
\* (Structural property, not a state invariant)

\* INV-10: BoundedHistory
\* History sent to LLM is bounded
BoundedHistory ==
    requestBody /= NULL =>
        requestBody.historyLen <= MaxHistory

\* --- LIVENESS PROPERTIES ---

\* Every generation attempt eventually reaches idle
EventualCompletion == <>(phase = "idle")

\* isGenerating is eventually reset (weak fairness required)
EventualReset == isGenerating => <>(~isGenerating)

\* ===========================================================================
\* Target invariants (what SHOULD hold after the fix)
\* ===========================================================================

\* TARGET-INV-1: AttachmentPreservation (fixed)
\* TargetAttachmentPreservation ==
\*     \A i \in 1..Len(storedMessages) :
\*         storedMessages[i].role = "user" =>
\*             (filesAtSubmitTime /= {} => storedMessages[i].hasAttachments)

\* TARGET-INV-2: FileContentDelivery (fixed)
\* TargetFileContentDelivery ==
\*     \A i \in 1..Len(storedMessages) :
\*         storedMessages[i].hasAttachments =>
\*             openaiContent = "multipart"

\* TARGET-INV-3: AttachmentRenderability (fixed)
\* TargetAttachmentRenderability ==
\*     \A i \in 1..Len(storedMessages) :
\*         storedMessages[i].hasAttachments => TRUE  \* Renderable

=============================================================================
```

## Change Impact Analysis

**Proposed change:** User can attach a file and the file is sent to the LLM along with the user input.

**Affected steps:**

| Step | Current | Required change |
|------|---------|-----------------|
| 1. files_selected | Files stored but read side discarded | Expose files getter: `const [files, setFiles] = useState<File[]>([])` |
| 2. message_submitted | `onSendMessage(string)` — text only | Either widen signature to `onSendMessage(string, File[])` or have `handleSendMessage` read files directly from state |
| 4. user_msg_stored | `addMessage({role, content, timestamp})` | Include `attachments: files.map(f => ({id, filename, size, type}))` + read file content |
| 5. generating | `generateResponse(content, history)` — no files | Add files/attachments parameter, serialize file content (base64 or FormData) |
| 6. openai_messages_built | `content: string` always | Convert to `content: ContentPart[]` when attachments present: `[{type:'text', text:msg}, {type:'image_url', image_url:{url:dataUrl}}]` for images, or prepend file text content to prompt for documents |
| 10. files_cleared | No-op cleanup | Now meaningful: clears actually-used files |
| (postcondition) MessageBubble | Only renders `message.content` | Render attachment indicators (filename, icon, size) when `message.attachments` is non-empty |

**Affected invariants:**

| Invariant | Impact |
|-----------|--------|
| INV-1 (AttachmentPreservation) | **Must be fixed** — core of the feature |
| INV-2 (FileContentDelivery) | **Must be fixed** — requires type-level change to multipart content |
| INV-3 (AttachmentRenderability) | **Should be fixed** — UX requirement for user to see their attachments |
| INV-4 (FileValidationGuard) | Unaffected — validation logic stays the same |
| INV-5 (ResponseCompleteness) | Unaffected — try/catch structure preserved |
| INV-6 (GeneratingFlagReset) | Unaffected — finally block preserved |
| INV-7 (FileCleanup) | Semantics change: no longer no-op, now clearing used data |
| INV-8 (BoundedRetry) | Unaffected — retry logic stays the same |
| INV-9 (ImmediateErrorPropagation) | Unaffected |
| INV-10 (BoundedHistory) | Unaffected — history slicing stays the same |

**Risk:** Naive implementation could break INV-5 if file reading throws before the try block, or break INV-6 if file serialization errors aren't caught by the existing try/catch. The file-to-base64 conversion should happen inside the existing try block.

**Recommendation:** Extend the model first — add `filesAtSubmitTime` as a snapshot variable captured at step 2, thread it through steps 4-6, and re-verify that TARGET-INV-1/2/3 hold while INV-4 through INV-10 are preserved. Then use the extended model as the spec for `/create_tdd_plan`.
