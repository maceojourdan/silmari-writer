# process-voice-input-and-progress-session TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/307-process-voice-input-and-progress-session.md

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/307-process-voice-input-and-progress-session.md`

Stdout excerpt:
```
Path: process-voice-input-and-progress-session
Result: ALL PROPERTIES PASSED
States: 26 found, 13 distinct, depth 0
Properties: Reachability, TypeInvariant, ErrorConsistency
```

This TDD plan translates those proven properties directly into code-level assertions.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/VoiceSessionComponent.tsx` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/submitVoiceResponse.ts` |
| api-m5g7 | endpoint | `app/api/session/voice-response/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/ProcessVoiceResponseHandler.ts` |
| db-h2s4 | service | `backend/services/SessionProgressionService.ts` |
| db-b7r2 | processor | `backend/processors/VoiceResponseProcessor.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/SessionDAO.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/SessionErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |
| ui-y5t3 | data_loader | `frontend/data_loaders/useSessionDataLoader.ts` |

Tech stack: Option 1 – Next.js (App Router), TypeScript, Zod, Vitest.

---

## Step 1: Capture voice input

**From path spec:**
- Input: Voice audio stream from user within active session context in INIT state via ui-w8p2
- Process: Capture spoken input, associate with active session ID, prepare structured payload
- Output: Structured voice input payload `{ sessionId, transcript }`
- Error: No active session or microphone access fails → display error and prevent submission

### Test (`frontend/components/__tests__/VoiceSessionComponent.test.tsx`)

- [x] Reachability: render component with active session in INIT, simulate transcript event → expect payload builder called with `{ sessionId, transcript }`.
- [x] TypeInvariant: assert payload matches `SubmitVoiceResponseRequest` TypeScript type.
- [x] ErrorConsistency:
  - [x] No active session → expect error banner and no API call.
  - [x] Mic permission denied → expect error message and logger call.

### Implementation (`frontend/components/VoiceSessionComponent.tsx`)

- [x] Read active session from state.
- [x] On transcript final event, construct:
  ```ts
  const payload: SubmitVoiceResponseRequest = {
    sessionId,
    transcript
  }
  ```
- [x] Guard clauses:
  - [x] If no session → throw/display `SharedErrors.NO_ACTIVE_SESSION`.
  - [x] If mic failure → log via `frontend/logging` and show error.

---

## Step 2: Submit voice response to backend endpoint

**From path spec:**
- Input: Structured payload via api-q7v1 to api-m5g7
- Process: POST to backend endpoint
- Output: HTTP request received by backend
- Error: Network/auth failure → cfg-j9w2 error and user-visible message

### Test (`frontend/api_contracts/__tests__/submitVoiceResponse.test.ts`)

- [x] Reachability: mock `fetch` success → expect POST to `/api/session/voice-response` with correct JSON body.
- [x] TypeInvariant: response parsed as `SubmitVoiceResponseResponse`.
- [x] ErrorConsistency:
  - [x] 401 → expect `SharedErrors.UNAUTHORIZED`.
  - [x] Network reject → expect `SharedErrors.NETWORK_ERROR` and surfaced message.

### Implementation (`frontend/api_contracts/submitVoiceResponse.ts`)

- [x] Zod schema for request/response.
- [x] `fetch` POST with JSON.
- [x] Map HTTP errors to `SharedErrors`.

---

## Step 3: Handle and validate request

**From path spec:**
- Input: HTTP request at api-m5g7 routed to api-n8k2
- Process: Validate session state (INIT or valid intermediate), verify payload, forward to service
- Output: Validated command
- Error: Invalid state or payload → db-l1c3 domain error

### Test (`backend/request_handlers/__tests__/ProcessVoiceResponseHandler.test.ts`)

- [x] Reachability: valid INIT session + valid payload → expect service called with validated command.
- [x] TypeInvariant: handler input conforms to Zod schema; output is service result type.
- [x] ErrorConsistency:
  - [x] Session not INIT → expect `SessionErrors.INVALID_STATE`.
  - [x] Invalid payload → expect `SessionErrors.INVALID_PAYLOAD`.

### Implementation

- [x] Zod validation of body.
- [x] Fetch session via `SessionDAO`.
- [x] If state invalid → throw `SessionErrors.INVALID_STATE`.
- [x] Forward to `SessionProgressionService`.

---

## Step 4: Process response and update session

**From path spec:**
- Input: Validated command to db-h2s4
- Process: Orchestrate db-b7r2 processor + db-d3w8 DAO; determine next state; persist StoryRecord
- Output: Persisted StoryRecord + transitioned session state
- Error: Persistence failure or invalid transition → log via cfg-q9c5 and raise db-l1c3 error

### Test (`backend/services/__tests__/SessionProgressionService.test.ts`)

- [x] Reachability: given INIT session + transcript →
  - [x] processor returns next state
  - [x] DAO persists updated session + StoryRecord
  - [x] expect returned updated entities.
- [x] TypeInvariant: returned object matches `SessionWithStoryRecord` type.
- [x] ErrorConsistency:
  - [x] Invalid transition → `SessionErrors.INVALID_TRANSITION`.
  - [x] DAO throws → service logs via backend logger and throws `SessionErrors.PERSISTENCE_FAILED`.

### Implementation

- [x] `VoiceResponseProcessor.process(transcript, session)` → `{ nextState, updatedStoryRecord }`.
- [x] Validate state transition rules.
- [x] `SessionDAO.updateSessionAndStoryRecord()` transactional call.
- [x] Catch errors → log via `backend/logging` → rethrow domain error.

---

## Step 5: Return updated session to frontend

**From path spec:**
- Input: Updated session + StoryRecord
- Process: Construct HTTP response
- Output: 200 JSON response
- Error: Response construction fails → cfg-j9w2 standardized error + log

### Test (`app/api/session/voice-response/__tests__/route.test.ts`)

- [x] Reachability: mock handler success → expect 200 JSON with updated session.
- [x] TypeInvariant: response matches Zod response schema.
- [x] ErrorConsistency:
  - [x] Handler throws domain error → expect mapped `SharedErrors.DOMAIN_ERROR` with correct status code.

### Implementation

- [x] Next.js `POST` route.
- [x] Call `ProcessVoiceResponseHandler`.
- [x] Wrap in try/catch:
  - [x] Map domain errors to HTTP codes.
  - [x] Log failures.

---

## Step 6: Update UI with progressed session

**From path spec:**
- Input: Successful HTTP response via api-q7v1 consumed by ui-y5t3 and rendered in ui-w8p2
- Process: Update local state; reflect new state; display updated StoryRecord
- Output: UI shows progressed session state and answers
- Error: UI state update fails → log via cfg-r3d7 and show recoverable error

### Test (`frontend/data_loaders/__tests__/useSessionDataLoader.test.tsx`)

- [x] Reachability: mock successful API response → expect state updated and component re-rendered with new state.
- [x] TypeInvariant: state matches `SessionState` + `StoryRecord` types.
- [x] ErrorConsistency:
  - [x] State update throws → logger called and error message rendered.

### Implementation

- [x] React hook `useSessionDataLoader` wraps API call.
- [x] On success → setSession(updatedSession).
- [x] Catch errors → log via `frontend/logging`; set recoverable UI error state.

---

## Terminal Condition

### Integration Test (`__tests__/processVoiceInput.integration.test.ts`)

Exercise full path:
1. [x] Render component with INIT session.
2. [x] Simulate transcript.
3. [x] Mock backend service + DAO.
4. [x] Assert:
   - [x] Session state transitions from INIT → next intermediate state.
   - [x] StoryRecord contains captured answer.
   - [x] UI displays updated state and answer.

Assertions:
- [x] Reachability: Trigger → all 6 steps executed.
- [x] TypeInvariant: Types preserved across frontend → API → backend → DB → frontend.
- [x] ErrorConsistency: Inject failure at each boundary and assert defined error surfaces.

---

## References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/307-process-voice-input-and-progress-session.md
- Gate 1: F-EPIC-SESSION (acceptance criterion 3)
- Gate 2: Option 1 – Next.js + Supabase
