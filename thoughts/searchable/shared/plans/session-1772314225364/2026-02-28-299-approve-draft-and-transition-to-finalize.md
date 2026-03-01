# approve-draft-and-transition-to-finalize TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/299-approve-draft-and-transition-to-finalize.md`

Tech Stack (Gate 2 – Option 1):
- Frontend: Next.js (App Router), React, TypeScript, Vitest
- Backend: Next.js API Routes (Node.js, TypeScript, Zod)
- Database: Supabase (Postgres)

---

## Verification (Phase 0)

The TLA+ model for this path passed all properties.

Command:
`sudo silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/299-approve-draft-and-transition-to-finalize.md`

Stdout excerpt:
- `Result: ALL PROPERTIES PASSED`
- `States: 26 found, 13 distinct`

Verified properties:
- Reachability
- TypeInvariant
- ErrorConsistency

These properties will be mirrored as:
- Reachability → Step callable from trigger to terminal
- TypeInvariant → Zod + TS type assertions at boundaries
- ErrorConsistency → Explicit error types returned and asserted

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/ApproveButton.tsx` |
| ui-v3n6 | module | `frontend/modules/DraftSessionView.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/sessionStateVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/approveSession.ts` |
| api-m5g7 | endpoint | `app/api/sessions/[id]/approve/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/ApproveSessionHandler.ts` |
| db-h2s4 | service | `backend/services/SessionApprovalService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/SessionDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Session.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/PersistenceErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/StateTransitionErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/approvalLogger.ts` |
| cfg-p4b8 | shared_logging | `shared/logging/index.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/clientLogger.ts` |

---

## Step 1: Capture Approve Action ✅

**From path spec:**
- Input: User interaction on Approve control (ui-w8p2) within module (ui-v3n6).
- Process: Capture event and prepare approval request.
- Output: Structured approval request payload `{ sessionId, action: 'APPROVE' }`.
- Error: If session not in DRAFT, block via frontend_verifier (ui-a4y1).

### Test (`frontend/components/__tests__/ApproveButton.test.tsx`) ✅

- [x] Reachability:
  - Render `DraftSessionView` with session `{ id, state: 'DRAFT' }`
  - Click Approve
  - Assert API contract called with `{ sessionId, action: 'APPROVE' }`

- [x] TypeInvariant:
  - Assert payload satisfies `ApproveSessionRequestSchema`

- [x] ErrorConsistency:
  - Render with state `FINALIZE`
  - Click Approve
  - Assert verifier blocks call
  - Assert validation message rendered

### Implementation ✅

- [x] `sessionStateVerifier.ts`
  - `assertDraft(session)` throws `InvalidStateTransitionError` if not DRAFT.
- [x] `ApproveButton.tsx`
  - OnClick → call verifier → build typed payload → call API contract.
- [x] Define `ApproveSessionRequestSchema` (Zod) in API contract.

---

## Step 2: Invoke Approval Endpoint ✅

**From path spec:**
- Input: Approval payload via api-q7v1.
- Process: Submit to backend endpoint.
- Output: HTTP request delivered.
- Error: Network failure → user-visible error + log via cfg-r3d7.

### Test (`frontend/api_contracts/__tests__/approveSession.test.ts`) ✅

- [x] Reachability:
  - Mock fetch 200
  - Call `approveSession()`
  - Assert POST to `/api/sessions/{id}/approve`

- [x] TypeInvariant:
  - Assert request + response validated via Zod schemas

- [x] ErrorConsistency:
  - Mock fetch reject
  - Assert error surfaced to caller
  - Assert `clientLogger.error` called
  - Assert no UI state mutation

### Implementation ✅

- [x] `approveSession.ts`
  - Typed function using fetch
  - Zod validation on response
  - try/catch → log via `clientLogger`

---

## Step 3: Process Approval Request ✅

**From path spec:**
- Input: Request handled by api-n8k2 → db-h2s4.
- Process: Validate exists + DRAFT → orchestrate transition.
- Output: Validated instruction to update state to FINALIZE.
- Error: Not found or not DRAFT → shared_error_definitions.

### Test (`backend/services/__tests__/SessionApprovalService.test.ts`) ✅

- [x] Reachability:
  - Mock DAO returning session `{ state: 'DRAFT' }`
  - Call service.approve(sessionId)
  - Assert returns transition instruction `{ newState: 'FINALIZE' }`

- [x] TypeInvariant:
  - Assert returned object matches `SessionTransitionResult` type

- [x] ErrorConsistency:
  - DAO returns null → expect `SessionNotFoundError`
  - DAO returns state FINALIZE → expect `InvalidStateTransitionError`

### Implementation ✅

- [x] `SessionApprovalService.approve(sessionId)`
  - Load via DAO
  - Validate state === DRAFT
  - Return transition instruction
  - Throw errors from `StateTransitionErrors.ts`

---

## Step 4: Persist Session State Transition ✅

**From path spec:**
- Input: Validated transition + DAO.
- Process: Update DB state DRAFT → FINALIZE.
- Output: Persisted session record.
- Error: DB failure → backend_error_definitions; no approval log.

### Test (`backend/data_access_objects/__tests__/SessionDAO.test.ts`) ✅

- [x] Reachability:
  - Mock Supabase update success
  - Assert state updated to FINALIZE

- [x] TypeInvariant:
  - Assert returned entity conforms to `Session` schema (db-f8n5)

- [x] ErrorConsistency:
  - Mock DB error
  - Expect `PersistenceError`
  - Assert approvalLogger not called

### Implementation ✅

- [x] `Session.ts` → define Zod schema with `state` enum.
- [x] `SessionDAO.updateState(id, 'FINALIZE')`
- [x] Throw `PersistenceError` on failure.

---

## Step 5: Log Approval Event ✅

**From path spec:**
- Input: Successful transition + sessionId.
- Process: Log event with sessionId, APPROVE, timestamp.
- Output: Log entry stored.
- Error: Logging fails → fallback via shared_logging and return error.

### Test (`backend/logging/__tests__/approvalLogger.test.ts`) ✅

- [x] Reachability:
  - Mock primary logger success
  - Assert log entry written

- [x] TypeInvariant:
  - Assert log entry shape `{ sessionId, action: 'APPROVE', timestamp }`

- [x] ErrorConsistency:
  - Mock logger throw
  - Assert fallback logger called
  - Assert service returns logging failure error

### Implementation ✅

- [x] `approvalLogger.logApproval(sessionId)`
  - Write to backend log store
  - Catch → call shared logger → rethrow

---

## Step 6: Return Updated Session to UI ✅

**From path spec:**
- Input: Updated session FINALIZE + logged approval.
- Process: Endpoint returns success; UI updates state.
- Output: UI displays FINALIZE + confirmation.
- Error: Client response handling fails → generic error, no mutation.

### Test (`frontend/modules/__tests__/DraftSessionView.test.tsx`) ✅

- [x] Reachability:
  - Mock API returns `{ state: 'FINALIZE' }`
  - Click Approve
  - Await UI update
  - Assert status label shows FINALIZE
  - Assert confirmation message visible

- [x] TypeInvariant:
  - Assert response matches `Session` schema

- [x] ErrorConsistency:
  - Mock malformed response
  - Assert generic error displayed
  - Assert state unchanged

### Implementation ✅

- [x] API route `route.ts`
  - Call handler → service → DAO → logger
  - Return 200 JSON session
- [x] UI state updated via React state setter

---

## Terminal Condition ✅

### Integration Test (`__tests__/approveSession.integration.test.ts`) ✅

- [x] Seed session in DRAFT
- [x] Simulate approval flow
- [x] Assert:
  - DB state = FINALIZE
  - approval log entry exists (cfg-q9c5)
  - UI displays FINALIZE + confirmation

This proves:
- [x] Reachability: trigger → all 6 steps → terminal
- [x] TypeInvariant: all schema boundaries validated
- [x] ErrorConsistency: each failure branch produces defined error

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/299-approve-draft-and-transition-to-finalize.md`
- Gate 1: F-REVIEW-APPROVE
- Gate 2: Option 1 – Next.js + Supabase
