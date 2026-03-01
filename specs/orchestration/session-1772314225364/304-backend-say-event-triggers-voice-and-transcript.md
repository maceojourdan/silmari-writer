# PATH: backend-say-event-triggers-voice-and-transcript

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

Backend emits SAY event for a user with an active session

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `mq-r4z8` | backend_process_chain | Routes SAY and TRANSCRIPT_FINAL events through backend processing stages |
| `db-j6x9` | backend_verifier | Validates active session state and SAY payload structure |
| `cfg-h5v9` | transformer | Transforms prompt text into structured speech synthesis request |
| `cfg-j9w2` | shared_error_definitions | Provides standardized error codes for validation, synthesis, and dispatch failures |
| `cfg-q9c5` | backend_logging | Logs backend processing, synthesis retries, and dispatch errors |
| `ui-v3n6` | module | Frontend conversation/voice module that receives and displays transcript events |
| `ui-a4y1` | frontend_verifier | Validates transcript data before rendering in UI |
| `cfg-r3d7` | frontend_logging | Logs UI-side rendering or validation errors |

## Steps

1. **Intercept SAY event**
   - Input: SAY event emitted through mq-r4z8 (backend_process_chain) for a session-bound user
   - Process: Middleware execution pattern evaluates the event type and routes SAY events to the voice handling middleware chain.
   - Output: SAY event forwarded to middleware voice processing chain with associated session context
   - Error: If event payload is malformed or missing required fields, raise standardized error using cfg-j9w2 (shared_error_definitions) and log via cfg-q9c5 (backend_logging), then abort processing.

2. **Validate session context**
   - Input: Forwarded SAY event with session identifier and payload
   - Process: Apply backend verification rules to confirm the session is active and the payload structure matches expected schema.
   - Output: Validated SAY command with confirmed active session context
   - Error: If session is inactive or validation fails, reject event using db-j6x9 (backend_verifier) and emit standardized error from cfg-j9w2 (shared_error_definitions); log via cfg-q9c5 (backend_logging).

3. **Transform prompt to speech request**
   - Input: Validated SAY command containing text prompt
   - Process: Convert prompt text into a speech synthesis request format required by the voice subsystem.
   - Output: Structured speech synthesis request payload
   - Error: If transformation fails due to invalid text format, return transformation error defined in cfg-j9w2 and log via cfg-q9c5.

4. **Synthesize and stream audio**
   - Input: Structured speech synthesis request payload
   - Process: Invoke voice agent to synthesize audio and stream the generated speech to the client over the active session channel.
   - Output: Audio stream delivered to client and internal transcript text captured
   - Error: If synthesis or streaming fails, retry up to 2 times; after final failure, emit error event defined in cfg-j9w2 and log via cfg-q9c5.

5. **Emit TRANSCRIPT_FINAL event**
   - Input: Finalized transcript text associated with SAY event
   - Process: Package transcript into TRANSCRIPT_FINAL event and dispatch through backend process chain to the frontend session channel.
   - Output: TRANSCRIPT_FINAL event delivered to frontend module for rendering
   - Error: If dispatch fails, retry up to 2 times; on persistent failure, log via cfg-q9c5 and surface standardized error from cfg-j9w2.

6. **Render transcript in UI**
   - Input: TRANSCRIPT_FINAL event received by ui-v3n6 (module)
   - Process: Update conversation state and render transcript message within the active voice/chat interface component.
   - Output: User sees finalized transcript text in conversation view synchronized with spoken prompt
   - Error: If UI update fails validation, handle via ui-a4y1 (frontend_verifier) and log via cfg-r3d7 (frontend_logging); display fallback error message to user.

## Terminal Condition

User hears the spoken prompt from the voice agent and sees the finalized transcript message delivered via TRANSCRIPT_FINAL in the UI conversation view

## Feedback Loops

If speech synthesis or transcript streaming fails, retry TTS generation and transcript dispatch up to 2 additional times before emitting a failure event and logging the error.
