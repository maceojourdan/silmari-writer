# PATH: file-to-llm-pipeline-target

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 2
**Source:** Extended from `file-to-llm-pipeline-model` (baseline). Adds file-forwarding states to fix INV-1, INV-2, INV-3.

## Purpose

Target behavioral model for the file-attachment-to-LLM pipeline. This extends
the baseline model to close the data-loss gap where attached files are silently
dropped. All 10 original invariants must hold in this model — the 3 previously
violated invariants (INV-1, INV-2, INV-3) are now enforced, and the 7 that
already held (INV-4 through INV-10) are preserved.

Key structural changes from baseline:
- `filesAccessible` flipped from FALSE to TRUE (fix page.tsx:26 destructuring)
- New state variable `filesAtSubmitTime` captures file snapshot at send
- New step `file_content_prepared` reads and converts file content
- `requestBody` now carries attachments when files present
- `openaiContent` is conditionally multipart when attachments present
- `MessageBubble` renders attachment indicators (postcondition fixed)

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

## Steps

1. **files_selected** — User attaches files via FileAttachment
   - Input: FileList or File array from drag-and-drop or file picker
   - Process: validateAndAddFiles at FileAttachment.tsx:45 validates size and count constraints then merges valid files into component state and calls onFilesChange to notify parent
   - Output: File array delivered to parent page.tsx via setFiles with getter now accessible
   - Error: Files exceeding maxSizeBytes or maxFiles limit are rejected with error message displayed in FileAttachment UI

2. **message_submitted** — User sends text and files are snapshotted
   - Input: Content string from MessageInput.handleSubmit and files array from page.tsx state
   - Process: Trim content and guard against empty. Read files from state getter which is now accessible. Capture filesAtSubmitTime as a snapshot of current files. Call handleSendMessage with content string.
   - Output: Content string and filesAtSubmitTime snapshot passed to orchestration layer
   - Error: Empty content is silently ignored and no action taken

3. **guard_check** — Verify active project exists
   - Input: Content string and filesAtSubmitTime from step 2
   - Process: Check activeProjectId at page.tsx. If null return early to idle. If present clear error state and proceed.
   - Output: Confirmed activeProjectId and forwarded content plus filesAtSubmitTime

4. **user_msg_stored** — Add user message with attachments to Zustand store
   - Input: Content string, activeProjectId string, and filesAtSubmitTime snapshot
   - Process: Build attachments array by mapping each file in filesAtSubmitTime to an Attachment object with id filename size and type fields. Call addMessage with role user content timestamp and attachments array. Zustand generates UUID for message id. INV-1 is now satisfied because filesAtSubmitTime is accessible and attachments are populated.
   - Output: Message object stored with attachments field populated when files were present
   - Error: File metadata extraction failure prevents message storage

5. **file_content_prepared** — Read file contents and convert to API format
   - Input: filesAtSubmitTime array of File objects
   - Process: For each file read content as ArrayBuffer. For image files (image/png image/jpeg image/gif image/webp) convert to base64 data URL. For text files (text/plain application/json) extract text content. For PDF files extract text or convert to base64. Produce an array of FileContentPayload objects with filename contentType and either textContent or base64Data fields.
   - Output: Array of prepared file content payloads ready for API serialization
   - Error: File read failure or unsupported content type produces error. Individual file failures are isolated and do not block other files.

6. **generating** — Build and send API request with file data
   - Input: Content string, activeMessages array, and prepared file content payloads from step 5
   - Process: generateResponse at api.ts builds request body with message string history bounded to last 10 messages and attachments array containing file content payloads. POST to /api/generate with Content-Type application/json. INV-2 is now satisfied because file data is included in request body. INV-10 preserved because history is still bounded.
   - Output: Promise of response string from API
   - Error: Network failure or non-ok response status throws error

7. **openai_messages_built** — Route handler builds multipart OpenAI messages
   - Input: Request body containing message history and attachments from step 6
   - Process: POST handler at route.ts validates message and API key. When attachments are present build content as multipart array with text part containing the user message and additional parts for each attachment. Image attachments become image_url content parts with base64 data URLs. Text attachments are prepended to the user message text. When no attachments are present content remains a plain string. Type changes from always-string to string or ContentPart array. INV-2 type-level fix is satisfied.
   - Output: OpenAI messages array with multipart content when attachments present
   - Error: Invalid message returns 400. Missing API key returns 500. Malformed attachments returns 400.

8. **openai_calling** — Call OpenAI with retry logic bounded by max 3 retries
   - Input: OpenAI client and messages array with potentially multipart content
   - Process: makeOpenAIRequest at route.ts calls openai.chat.completions.create with model temperature and max_tokens. Retry logic uses exponential backoff with 10s base for rate limits and 2s base for server errors. INV-8 preserved with bounded retries. INV-9 preserved with immediate propagation of non-retryable errors.
   - Output: Response text string extracted from completion choices
   - Error: 401 INVALID_API_KEY not retryable. 429 RATE_LIMIT retryable. 5xx API_ERROR retryable. Other status API_ERROR not retryable. No status NETWORK retryable. Null content API_ERROR not retryable.

9. **response_received** — Extract and return LLM response
   - Input: Response text from step 8
   - Process: Route handler returns NextResponse.json with content field
   - Output: JSON response with content string delivered to client
   - Error: ChatGenerationError mapped to HTTP status 401 429 500 or 502. Unknown error returns 500 INTERNAL_ERROR.

10. **assistant_msg_stored** — Add assistant message to store
    - Input: Response string from API
    - Process: addMessage with role assistant content response and timestamp. INV-5 preserved because every generation call produces an assistant message or sets error.
    - Output: Assistant message stored in Zustand
    - Error: None

11. **files_cleared** — Cleanup resets state to idle
    - Input: None. Finally block at page.tsx runs on all paths.
    - Process: Set isGenerating to false. Clear files with setFiles empty array. Clear filesAtSubmitTime. INV-6 preserved because isGenerating always reset. INV-7 preserved because files always cleared. This cleanup is now meaningful because files were actually used.
    - Output: State fully reset to idle

## Terminal Condition

Success: User message with attachments stored in Zustand. LLM response informed by file content stored in Zustand. Both rendered in ConversationView via MessageBubble. Attachments displayed as indicators showing filename and type alongside message content. INV-3 postcondition is satisfied because MessageBubble now renders attachment indicators.

Failure: Error message displayed. isGenerating reset. Files and filesAtSubmitTime cleared. No assistant message stored. Partial work does not persist.

## Feedback Loops

Retry loop bounded by 3 at step 8 openai_calling. Rate limit errors use 10s base delay with exponential backoff. Server and network errors use 2s base delay with exponential backoff. Non-retryable errors exit immediately without retry. No other feedback loops exist.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Status |
|----|-----------|--------|---------------|--------|
| INV-1 | If files attached when send triggered they appear as attachments on stored user message | page.tsx step 4 | AttachmentPreservation | FIXED by exposing files getter and populating attachments |
| INV-2 | Content sent to OpenAI includes file data when files present | route.ts step 7 | FileContentDelivery | FIXED by multipart content construction |
| INV-3 | Stored messages with attachments are renderable in UI | MessageBubble postcondition | AttachmentRenderability | FIXED by rendering attachment indicators |
| INV-4 | File validation runs before files enter state | FileAttachment.tsx step 1 | FileValidationGuard | HOLDS unchanged |
| INV-5 | Every generateResponse produces assistant message or error | page.tsx steps 10 11 | ResponseCompleteness | HOLDS unchanged |
| INV-6 | isGenerating always reset to false on all paths | page.tsx step 11 | GeneratingFlagReset | HOLDS unchanged |
| INV-7 | Files always cleared after generation completes | page.tsx step 11 | FileCleanup | HOLDS now meaningful |
| INV-8 | OpenAI retries bounded at max 3 with exponential backoff | route.ts step 8 | BoundedRetry | HOLDS unchanged |
| INV-9 | Non-retryable errors propagate immediately without retry | route.ts step 8 | ImmediateErrorPropagation | HOLDS unchanged |
| INV-10 | Message history sent to LLM bounded to last 10 | api.ts step 6 | BoundedHistory | HOLDS unchanged |

## Change Impact Analysis

**Changes from baseline model:**

| Component | Baseline | Target |
|-----------|----------|--------|
| page.tsx:26 | `const [, setFiles]` read side discarded | `const [files, setFiles]` getter exposed |
| page.tsx handleSendMessage | Receives only string | Reads files from state, snapshots as filesAtSubmitTime |
| page.tsx step 4 | addMessage without attachments | addMessage with attachments mapped from filesAtSubmitTime |
| NEW step 5 | Did not exist | file_content_prepared reads and converts file content |
| api.ts generateResponse | `{message, history}` only | `{message, history, attachments}` with file payloads |
| route.ts POST | content always string | content is string or multipart ContentPart array |
| route.ts makeOpenAIRequest | messages typed string content | messages typed string or ContentPart array content |
| MessageBubble | Only renders message.content | Also renders attachment indicators |
| page.tsx cleanup | No-op file clearing | Meaningful clearing of used files and snapshot |

**New step added:** Step 5 `file_content_prepared` sits between user_msg_stored and generating. This step reads file bytes and converts them to the format needed by the API. It can fail (file read error, unsupported type) and has its own error branch.

**Risk mitigations:**
- File content preparation (step 5) must be inside the existing try block to preserve INV-5 and INV-6
- Base64 encoding of large files could exceed request size limits. Consider adding a file size check specific to API payload limits separate from the UI maxSizeBytes limit.
- Multipart content format must match OpenAI API expectations exactly or the API call will fail at step 8 with a non-retryable error
