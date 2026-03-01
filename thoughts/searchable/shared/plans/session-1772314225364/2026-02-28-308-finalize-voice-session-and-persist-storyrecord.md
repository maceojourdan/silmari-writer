# finalize-voice-session-and-persist-storyrecord TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/308-finalize-voice-session-and-persist-storyrecord.md

Tech Stack (Gate 2 – Option 1):
- Frontend: Next.js (App Router), React, TypeScript, Vitest, Testing Library
- Backend: Next.js API Routes (Node.js, TypeScript, Zod)
- Database: Supabase (Postgres)

---

## Verification (Phase 0)

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/308-finalize-voice-session-and-persist-storyrecord.md
```

Result (from verification_results_json):

- Status: **verified**
- Exit code: `0`
- Properties passed:
  - Reachability
  - TypeInvariant
  - ErrorConsistency
- TLC: `ALL PROPERTIES PASSED`
- States: 26 found, 13 distinct

This TDD plan mirrors those three properties at code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/FinalizeSessionButton.tsx` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/finalizeSession.ts` |
| api-m5g7 | endpoint | `frontend/app/api/sessions/[id]/finalize/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/FinalizeSessionRequestHandler.ts` |
| db-h2s4 | service | `backend/services/FinalizeSessionService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/SessionStoryRecordDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Session.ts`, `StoryRecord.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/FinalizeErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/RequestErrors.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

---

## Step 1: Submit finalize session request ✅

**From path spec:**
- Input: UI interaction invoking frontend API contract with active session identifier.
- Process: Send finalize-session request with active session ID.
- Output: HTTP request received by backend endpoint.
- Error: If malformed or missing session ID → validation error (cfg-j9w2).

### Test (Frontend + API Contract)
`frontend/__tests__/finalizeSession.contract.test.ts`

- Reachability:
  - Call `finalizeSession({ sessionId: "s1" })`
  - Assert fetch is called with `POST /api/sessions/s1/finalize`
- TypeInvariant:
  - Assert request body schema matches Zod contract `{ sessionId: string }`
- ErrorConsistency:
  - Call with `{}` or undefined sessionId
  - Assert rejection with `RequestValidationError` from `shared/error_definitions/RequestErrors`

### Implementation
- Zod schema in `finalizeSession.ts`.
- Throw `RequestValidationError` if sessionId missing.
- API route validates params before calling handler.

---

## Step 2: Validate session eligibility for finalization ✅

**From path spec:**
- Input: session ID in request_handler → service.
- Process: Verify session exists, is ACTIVE, and required voice inputs complete.
- Output: Validated active session eligible.
- Error: If not exists/not active/incomplete → domain error (db-l1c3).

### Test
`backend/__tests__/FinalizeSessionService.validate.test.ts`

- Reachability:
  - Mock DAO to return session `{ id: "s1", state: "ACTIVE", requiredInputsComplete: true }`
  - Assert service returns validated session.
- TypeInvariant:
  - Assert returned object conforms to `Session` type.
- ErrorConsistency:
  - DAO returns null → expect `SessionNotFoundError`.
  - DAO returns state !== ACTIVE → expect `InvalidSessionStateError`.
  - requiredInputsComplete false → expect `IncompleteSessionError`.

### Implementation
- `FinalizeSessionService.validateEligibility(sessionId)`
- Use DAO `findSessionById`.
- Throw typed errors from `FinalizeErrors.ts`.

---

## Step 3: Update session state to FINALIZE ✅

**From path spec:**
- Input: Validated session entity.
- Process: Change state to FINALIZE and persist.
- Output: Session record stored with state FINALIZE.
- Error: Persistence failure → persistence error (db-l1c3), no partial updates.

### Test
`backend/__tests__/FinalizeSessionService.updateState.test.ts`

- Reachability:
  - Given validated session
  - Mock DAO `updateSessionState` resolves
  - Assert session.state === "FINALIZE"
- TypeInvariant:
  - Assert persisted entity matches `Session` type with state enum "FINALIZE".
- ErrorConsistency:
  - Mock DAO to throw DB error
  - Expect `SessionPersistenceError`
  - Assert StoryRecord not written (verify DAO not called for StoryRecord).

### Implementation
- Add `updateSessionState(sessionId, "FINALIZE")` in DAO.
- Wrap in transaction (Supabase RPC or explicit transaction).

---

## Step 4: Persist StoryRecord with FINALIZED status and responses ✅

**From path spec:**
- Input: Session in FINALIZE state + collected responses.
- Process: Create/update StoryRecord, set status FINALIZED, store responses.
- Output: StoryRecord persisted with status FINALIZED.
- Error: If persistence fails → rollback session state.

### Test
`backend/__tests__/FinalizeSessionService.persistStoryRecord.test.ts`

- Reachability:
  - Session in FINALIZE state
  - DAO `upsertStoryRecord` resolves
  - Assert returned StoryRecord.status === "FINALIZED"
  - Assert responses saved.
- TypeInvariant:
  - Assert returned object conforms to `StoryRecord` type.
- ErrorConsistency:
  - Mock `upsertStoryRecord` throws
  - Assert transaction rolls back:
    - Session state remains "ACTIVE"
  - Expect `StoryRecordPersistenceError`.

### Implementation
- DAO method `upsertStoryRecord(sessionId, responses, status)`.
- Transaction wrapper in service:
  - Begin
  - updateSessionState → upsertStoryRecord
  - On error → rollback and restore previous state.

---

## Step 5: Return confirmation response to user ✅

**From path spec:**
- Input: Successful session + StoryRecord persistence.
- Process: Construct success response with session state FINALIZE and StoryRecord status FINALIZED.
- Output: Frontend receives confirmation payload.
- Error: If response construction fails → log + generic failure.

### Test
`backend/__tests__/FinalizeSessionRequestHandler.response.test.ts`

- Reachability:
  - Mock service success
  - Call API route
  - Assert HTTP 200 with:
    ```json
    { "sessionState": "FINALIZE", "storyRecordStatus": "FINALIZED" }
    ```
- TypeInvariant:
  - Assert response matches typed contract in `api-q7v1`.
- ErrorConsistency:
  - Mock response builder throws
  - Assert generic 500 response
  - Assert error logged via backend logging.

### Implementation
- Request handler maps service result to DTO.
- Use Zod response schema.
- Catch unexpected errors and return 500.

---

## Step 6: Display finalized session state in UI ✅

**From path spec:**
- Input: Success response consumed by UI component.
- Process: Update UI state to FINALIZE + FINALIZED; show confirmation.
- Output: User sees confirmation.
- Error: If UI update fails → log via cfg-r3d7; show retry prompt.

### Test
`frontend/__tests__/FinalizeSessionButton.ui.test.tsx`

- Reachability:
  - Mock successful API response
  - Simulate click
  - Assert confirmation text visible:
    - "Session finalized"
    - "StoryRecord status: FINALIZED"
- TypeInvariant:
  - Assert component state matches:
    ```ts
    { sessionState: "FINALIZE", storyRecordStatus: "FINALIZED" }
    ```
- ErrorConsistency:
  - Mock API rejection
  - Assert logger called
  - Assert retry prompt rendered
  - Backend not re-called automatically.

### Implementation
- `FinalizeSessionButton.tsx`:
  - onClick → call contract
  - setState from payload
  - catch → log via `frontend/logging` and show retry UI.

---

## Terminal Condition ✅

### Integration Test
`integration/__tests__/finalizeSession.e2e.test.ts`

- Seed DB with ACTIVE session + completed inputs.
- Call API route end-to-end.
- Assert:
  - Session state in DB = "FINALIZE"
  - StoryRecord.status = "FINALIZED"
  - All responses persisted
  - HTTP 200 payload correct
  - UI test renders confirmation.

This proves:
- Reachability: trigger → all 6 steps → terminal condition.
- TypeInvariant: types preserved across UI → API → service → DB → response.
- ErrorConsistency: each failure path returns defined error without partial updates.

---

## References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/308-finalize-voice-session-and-persist-storyrecord.md
- Gate 1: F-EPIC-SESSION (Acceptance Criteria #4, #5)
- Gate 2: Option 1 – Next.js + Supabase
