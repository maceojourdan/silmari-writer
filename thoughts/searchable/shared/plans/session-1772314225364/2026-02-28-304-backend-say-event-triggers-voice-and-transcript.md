# backend-say-event-triggers-voice-and-transcript TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/304-backend-say-event-triggers-voice-and-transcript.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/304-backend-say-event-triggers-voice-and-transcript.md`

Stdout:
```
Path: backend-say-event-triggers-voice-and-transcript
TLA+ spec: .../304-backend-say-event-triggers-voice-and-transcript/BackendSayEventTriggersVoiceAndTranscript.tla
TLC config: .../304-backend-say-event-triggers-voice-and-transcript/BackendSayEventTriggersVoiceAndTranscript.cfg
Result: ALL PROPERTIES PASSED
States: 26 found, 13 distinct, depth 0
```

All three properties are satisfied at the model level and will be mapped to code-level tests below.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|---------------|------------------------|
| mq-r4z8 | backend_process_chain | `backend/process_chains/SayEventProcessChain.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/SaySessionVerifier.ts` |
| cfg-h5v9 | transformer | `shared/transformers/SpeechRequestTransformer.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/VoiceErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |
| ui-v3n6 | module | `frontend/modules/ConversationVoiceModule.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/TranscriptVerifier.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

Tech stack: Option 1 – Next.js (App Router), TypeScript, Vitest.

---

## Step 1: Intercept SAY event ✅

**From path spec:**
- Input: SAY event emitted through mq-r4z8 for a session-bound user
- Process: Middleware execution pattern evaluates event type and routes SAY events to voice handling middleware chain
- Output: SAY event forwarded to middleware voice processing chain with associated session context
- Error: If payload malformed/missing fields → standardized error (cfg-j9w2) + log (cfg-q9c5) + abort

### Test (`backend/process_chains/__tests__/SayEventProcessChain.step1.test.ts`)

- Reachability: call `handleEvent({ type: 'SAY', sessionId, text })`, assert forwarded to voice chain mock
- TypeInvariant: assert forwarded object matches `SayEventWithSessionContext` TypeScript type
- ErrorConsistency: call with `{ type: 'SAY', text: null }`, assert:
  - thrown/returned `VoiceErrors.INVALID_SAY_PAYLOAD`
  - logger called with error
  - voice chain NOT invoked

### Implementation (`backend/process_chains/SayEventProcessChain.ts`)

- Export `handleEvent(event)`
- Narrow on `event.type === 'SAY'`
- Zod schema validate payload
- On failure:
  - return/throw `VoiceErrors.INVALID_SAY_PAYLOAD`
  - call backend logger
- On success:
  - attach session context
  - call `handleVoiceSay(eventWithContext)` (next step entry)

---

## Step 2: Validate session context ✅

**From path spec:**
- Input: Forwarded SAY event with session identifier and payload
- Process: Confirm session active and payload schema valid
- Output: Validated SAY command with confirmed active session context
- Error: If inactive/invalid → reject via db-j6x9 + standardized error + log

### Test (`backend/verifiers/__tests__/SaySessionVerifier.step2.test.ts`)

- Reachability: call `validateActiveSession(event)` with active mock session → returns validated command
- TypeInvariant: assert return type `ValidatedSayCommand`
- ErrorConsistency:
  - inactive session → `VoiceErrors.SESSION_INACTIVE`
  - malformed schema → `VoiceErrors.INVALID_SAY_PAYLOAD`
  - logger called in both

### Implementation (`backend/verifiers/SaySessionVerifier.ts`)

- Function `validateActiveSession(event)`
- Query session store (mocked repository)
- If not active → error from `VoiceErrors`
- Return strongly typed validated object

---

## Step 3: Transform prompt to speech request ✅

**From path spec:**
- Input: Validated SAY command containing text prompt
- Process: Convert prompt text into speech synthesis request format
- Output: Structured speech synthesis request payload
- Error: If transformation fails → transformation error + log

### Test (`shared/transformers/__tests__/SpeechRequestTransformer.step3.test.ts`)

- Reachability: call `toSpeechRequest(validatedCommand)` → assert structured payload `{ text, voiceId, sessionId }`
- TypeInvariant: assert payload satisfies `SpeechSynthesisRequest` type
- ErrorConsistency: call with invalid text (empty string) → `VoiceErrors.TRANSFORMATION_FAILED` + logger called

### Implementation (`shared/transformers/SpeechRequestTransformer.ts`)

- Export `toSpeechRequest(cmd)`
- Validate non-empty text
- Map to ElevenLabs-compatible request object
- Throw `VoiceErrors.TRANSFORMATION_FAILED` on invalid

---

## Step 4: Synthesize and stream audio ✅

**From path spec:**
- Input: Structured speech synthesis request payload
- Process: Invoke voice agent, stream audio, capture transcript
- Output: Audio stream delivered + transcript text captured
- Error: Retry up to 2 times; after final failure emit error + log

### Test (`backend/services/__tests__/VoiceSynthesisService.step4.test.ts`)

- Reachability: mock ElevenLabs client success → assert:
  - `streamAudio` called once
  - transcript captured
- TypeInvariant: transcript returned as `string`
- ErrorConsistency:
  - mock failure twice then success → success after retry
  - mock failure 3 times → error `VoiceErrors.SYNTHESIS_FAILED`
  - logger called each failure

### Implementation (`backend/services/VoiceSynthesisService.ts`)

- Function `synthesizeAndStream(request)`
- For loop (max 3 attempts)
- On success: return transcript
- On final failure: throw `VoiceErrors.SYNTHESIS_FAILED`
- Use backend logger for each failure

---

## Step 5: Emit TRANSCRIPT_FINAL event ✅

**From path spec:**
- Input: Finalized transcript text
- Process: Package into TRANSCRIPT_FINAL event and dispatch through mq-r4z8
- Output: Event delivered to frontend session channel
- Error: Retry up to 2 times; persistent failure → log + standardized error

### Test (`backend/process_chains/__tests__/SayEventProcessChain.step5.test.ts`)

- Reachability: call `emitTranscriptFinal(transcript)` → assert dispatch called with `{ type: 'TRANSCRIPT_FINAL', text }`
- TypeInvariant: assert event matches `TranscriptFinalEvent` type
- ErrorConsistency:
  - mock dispatch fail twice then success → eventual success
  - mock fail 3 times → `VoiceErrors.TRANSCRIPT_DISPATCH_FAILED`
  - logger called

### Implementation (`backend/process_chains/SayEventProcessChain.ts`)

- Add `emitTranscriptFinal(transcript)`
- Retry loop (3 attempts)
- Dispatch via process chain
- Throw `VoiceErrors.TRANSCRIPT_DISPATCH_FAILED` on final failure

---

## Step 6: Render transcript in UI ✅

**From path spec:**
- Input: TRANSCRIPT_FINAL event received by ui-v3n6
- Process: Update conversation state and render transcript message
- Output: User sees finalized transcript text
- Error: If UI validation fails → handle via ui-a4y1 + log + fallback error message

### Test (`frontend/modules/__tests__/ConversationVoiceModule.step6.test.tsx`)

- Reachability: simulate receiving `TRANSCRIPT_FINAL` event → assert transcript rendered in DOM
- TypeInvariant: assert transcript passes `TranscriptVerifier` before state update
- ErrorConsistency:
  - invalid transcript payload →
    - verifier rejects
    - frontend logger called
    - fallback error message rendered

### Implementation (`frontend/modules/ConversationVoiceModule.tsx`)

- Subscribe to event stream
- On `TRANSCRIPT_FINAL`:
  - Validate with `TranscriptVerifier`
  - Update React state
  - Render message bubble
- On validation failure:
  - log via frontend logger
  - render fallback error component

---

## Terminal Condition ✅

### Integration Test (`__tests__/backend-say-event-triggers-voice-and-transcript.integration.test.ts`)

- Trigger: emit valid SAY event with active session
- Assert:
  - Audio synthesis service invoked
  - Transcript captured
  - TRANSCRIPT_FINAL dispatched
  - Frontend module renders transcript text

Terminal assertion:
- User hears spoken prompt (mock stream invoked)
- User sees finalized transcript in conversation view

This integration test proves:
- Reachability: full chain from SAY → UI render
- TypeInvariant: types preserved across boundaries
- ErrorConsistency: injected failures produce defined VoiceErrors

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/304-backend-say-event-triggers-voice-and-transcript.md`
- Gate 2 Tech Stack (Option 1 – Next.js + TypeScript)
- Verification results (Path 304, ALL PROPERTIES PASSED)
