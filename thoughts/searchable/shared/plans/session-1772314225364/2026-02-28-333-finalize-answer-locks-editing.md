# finalize-answer-locks-editing TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/333-finalize-answer-locks-editing.md

---

## Verification (Phase 0)

The TLA+ model for this path passed: **Reachability, TypeInvariant, ErrorConsistency**.

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/333-finalize-answer-locks-editing.md`

Verification output:

- Result: **ALL PROPERTIES PASSED**  
- States: 22 found, 11 distinct  
- Exit code: 0  
- Properties: Reachability, TypeInvariant, ErrorConsistency

This TDD plan ensures code-level tests assert the same properties proven at the model level.

---

## Tech Stack (Gate 2 – Option 1)

- **Frontend:** Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- **Backend:** Next.js API Routes (Node.js, TypeScript), Zod
- **Database:** Supabase (PostgreSQL)
- **Testing:** Vitest (unit), Supertest (API), Playwright (optional integration)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/FinalizeAnswerButton.tsx` |
| ui-v3n6 | module | `frontend/modules/answer/AnswerModule.tsx` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/finalizeAnswer.ts` |
| api-m5g7 | endpoint | `frontend/app/api/answers/[id]/finalize/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/FinalizeAnswerRequestHandler.ts` |
| db-b7r2 | processor | `backend/processors/FinalizeAnswerProcessor.ts` |
| db-h2s4 | service | `backend/services/AnswerFinalizeService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/AnswerDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Answer.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/AnswerFinalizeVerifier.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/FinalizeErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |

---

## Step 1: Capture Finalize Action

**From path spec:**  
- Input: User interaction event in ui-w8p2 within ui-v3n6  
- Process: Detect "Finalize", verify editable in local state, prepare request with answer ID  
- Output: Structured finalize request via api-q7v1  
- Error: If already finalized locally, block and show cfg-j9w2 error

### Test (`frontend/components/__tests__/FinalizeAnswerButton.test.tsx`)

- Reachability:  
  Render component with `{ editable: true, answerId }`, click button → assert `finalizeAnswer(answerId)` called.

- TypeInvariant:  
  Assert contract call matches Zod schema `{ answerId: string }`.

- ErrorConsistency:  
  Render with `{ editable: false }`, click → assert no API call and shared error message displayed from `SharedErrors.ANSWER_ALREADY_FINALIZED`.

### Implementation (`frontend/components/FinalizeAnswerButton.tsx`)

- Props: `{ answerId: string; editable: boolean }`
- On click:
  - If `!editable` → set local error from `SharedErrors`
  - Else call `finalizeAnswer({ answerId })`
- Disable button when not editable.

---

## Step 2: Handle Finalize API Request

**From path spec:**  
- Input: HTTP finalize request at api-m5g7  
- Process: Forward to api-n8k2 → db-b7r2  
- Output: Invocation of service with answerId + user context  
- Error: Auth/validation failure → db-l1c3 error

### Test (`backend/endpoints/__tests__/finalizeAnswer.route.test.ts`)

- Reachability:  
  POST `/api/answers/:id/finalize` with valid auth → expect processor invoked and 200 returned.

- TypeInvariant:  
  Invalid body (missing id) → 400 with Zod validation error.

- ErrorConsistency:  
  Missing/invalid auth → 401 with `FinalizeErrors.UNAUTHORIZED`.

### Implementation (`frontend/app/api/answers/[id]/finalize/route.ts`)

- Validate session (Supabase Auth)
- Parse params with Zod
- Call `FinalizeAnswerRequestHandler.handle({ answerId, user })`
- Map domain errors to HTTP codes

---

## Step 3: Validate and Lock Answer

**From path spec:**  
- Input: answerId + user context in db-h2s4  
- Process: Retrieve entity, verify completed & not finalized, update finalized=true & editable=false  
- Output: Persisted updated answer  
- Error: Not found / not completed / already finalized → db-l1c3 error, no state change

### Test (`backend/services/__tests__/AnswerFinalizeService.test.ts`)

- Reachability:  
  Given completed, editable answer → call finalize → assert DAO.update called with `{ finalized: true, editable: false }`.

- TypeInvariant:  
  Returned entity matches `Answer` type (id, finalized:boolean, editable:boolean).

- ErrorConsistency:
  - Not found → `FinalizeErrors.ANSWER_NOT_FOUND`
  - Not completed → `FinalizeErrors.ANSWER_NOT_COMPLETED`
  - Already finalized → `FinalizeErrors.ANSWER_ALREADY_FINALIZED`
  - Assert DAO.update NOT called in error cases.

### Implementation

- `AnswerDAO.findById(id)`
- `AnswerFinalizeVerifier.assertEligible(answer)`
- Update via `AnswerDAO.update(id, { finalized: true, editable: false })`
- Return updated entity

---

## Step 4: Return Finalized State to Frontend

**From path spec:**  
- Input: Updated entity  
- Process: Return via handler + endpoint  
- Output: HTTP success with finalized state  
- Error: Serialization failure → db-l1c3 error

### Test (`backend/request_handlers/__tests__/FinalizeAnswerRequestHandler.test.ts`)

- Reachability:  
  Mock service success → expect JSON `{ id, finalized: true, editable: false }`.

- TypeInvariant:  
  Response matches API contract schema.

- ErrorConsistency:  
  Simulate serialization throw → expect 500 with `FinalizeErrors.SERIALIZATION_ERROR`.

### Implementation

- Handler wraps processor result
- `return NextResponse.json(result)`
- Catch serialization → map to domain error

---

## Step 5: Update UI to Locked State

**From path spec:**  
- Input: Success response via api-q7v1  
- Process: Update local state to finalized and disable editing controls  
- Output: UI shows finalized, editing disabled  
- Error: Failure response → show cfg-j9w2 error, keep editable

### Test (`frontend/modules/answer/__tests__/AnswerModule.finalize.test.tsx`)

- Reachability:  
  Mock API success → assert editing controls removed/disabled and status label “Finalized” visible.

- TypeInvariant:  
  Local state updated to `{ finalized: true, editable: false }`.

- ErrorConsistency:  
  Mock API error → assert shared error shown and controls remain enabled.

### Implementation (`frontend/modules/answer/AnswerModule.tsx`)

- On finalize success:
  - `setAnswer({ ...answer, finalized: true, editable: false })`
- Conditionally render editing controls only if `editable`
- Display error from `SharedErrors` on failure

---

## Terminal Condition

### Integration Test (`tests/integration/finalizeAnswer.integration.test.ts`)

Exercise full path:

1. Seed DB with completed, editable answer.
2. Render UI.
3. Click Finalize.
4. Assert:
   - Backend row updated (`finalized = true`, `editable = false`).
   - HTTP 200 returned.
   - UI disables editing controls.

This proves:
- Reachability: Trigger → UI → API → Service → DB → UI
- TypeInvariant: Entity shape preserved across layers
- ErrorConsistency: No illegal state transitions occur

---

## References

- Path: 333-finalize-answer-locks-editing.md  
- Requirement: F-FINALIZE-EXPORT  
- Shared Errors: cfg-j9w2  
- Backend Errors: db-l1c3
