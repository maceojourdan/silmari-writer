# reject-modifications-to-finalized-session TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/309-reject-modifications-to-finalized-session.md

---

## Verification (Phase 0)
The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/309-reject-modifications-to-finalized-session.md`

Result (stdout excerpt):
- `Result: ALL PROPERTIES PASSED`
- `States: 22 found, 11 distinct, depth 0`
- `verify_exit_code: 0`

All three formal properties are satisfied and must be mirrored as test oracles at code level.

---

## Tech Stack (Gate 2)
Option 1 – Fastest Path
- Frontend: Next.js (App Router), React, TypeScript, Zod
- Backend: Next.js API Routes, Node.js, TypeScript
- Database: Supabase (PostgreSQL)
- Test Runner: Vitest (unit) + Playwright (optional integration)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|---------------|------------------------|
| ui-w8p2 | component | `frontend/components/SessionControls.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/SessionModificationVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/modifySession.ts` |
| api-m5g7 | endpoint | `app/api/sessions/[sessionId]/modify/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/ModifySessionRequestHandler.ts` |
| db-h2s4 | service | `backend/services/SessionModificationService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/StoryRecordDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/StoryRecord.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/StoryRecordStateVerifier.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/SessionErrors.ts` |

---

## Step 1: Submit modification request ✅

**From path spec:**
- [x] Input: User action in UI component (ui-w8p2) triggers frontend API contract (api-q7v1) call with session ID and action type
- [x] Process: Frontend sends request to backend endpoint
- [x] Output: HTTP request with sessionId + modificationAction
- [x] Error: If payload malformed, frontend_verifier (ui-a4y1) blocks submission

### Test (`frontend/components/__tests__/SessionControls.test.tsx`) ✅

- [x] Reachability: simulate click “Add Voice Input” with valid `sessionId`, assert `modifySession()` called.
- [x] TypeInvariant: assert payload matches:
  ```ts
  { sessionId: string; action: 'ADD_VOICE' | 'FINALIZE' }
  ```
- [x] ErrorConsistency: pass invalid payload (missing sessionId), assert verifier prevents call and displays validation error.

### Implementation ✅

- [x] `SessionModificationVerifier.ts` using Zod schema.
- [x] `modifySession.ts` exports typed function calling `/api/sessions/[sessionId]/modify`.
- [x] `SessionControls.tsx` calls verifier before invoking contract.

---

## Step 2: Route request to handler ✅

**From path spec:**
- [x] Input: HTTP request received by endpoint (api-m5g7)
- [x] Process: Endpoint validates request shape and forwards to request handler (api-n8k2)
- [x] Output: Structured command object
- [x] Error: If validation fails, return 4xx using backend_error_definitions (db-l1c3)

### Test (`app/api/sessions/[sessionId]/modify/__tests__/route.test.ts`) ✅

- [x] Reachability: POST valid JSON → expect handler invoked with typed command.
- [x] TypeInvariant: assert handler receives:
  ```ts
  type ModifySessionCommand = {
    sessionId: string;
    action: 'ADD_VOICE' | 'FINALIZE';
  }
  ```
- [x] ErrorConsistency: send malformed body → expect 400 + `INVALID_REQUEST` from `SessionErrors`.

### Implementation ✅

- [x] Zod schema in route.
- [x] Map validation errors to `SessionErrors.InvalidRequest`.
- [x] Forward typed object to `ModifySessionRequestHandler.handle()`.

---

## Step 3: Load StoryRecord ✅

**From path spec:**
- [x] Input: Structured command with session ID
- [x] Process: Service queries DAO to retrieve StoryRecord
- [x] Output: StoryRecord entity (expected FINALIZED)
- [x] Error: If not found, produce not-found error

### Test (`backend/services/__tests__/SessionModificationService.test.ts`) ✅

- [x] Reachability: mock DAO to return StoryRecord with state `FINALIZED`; assert service receives entity.
- [x] TypeInvariant: assert returned entity conforms to `StoryRecord` type with `state: 'INIT' | ... | 'FINALIZED'`.
- [x] ErrorConsistency: mock DAO returns null → expect `SessionErrors.NotFound`.

### Implementation ✅

- [x] `StoryRecord` type in `StoryRecord.ts` (existing).
- [x] `StoryRecordDAO.findById(sessionId)` (existing, reused).
- [x] Service throws `SessionErrors.NotFound` if null.

---

## Step 4: Verify session state ✅

**From path spec:**
- [x] Input: StoryRecord in FINALIZED state
- [x] Process: backend_verifier checks immutability rule
- [x] Output: Validation failure
- [x] Error: If verifier logic missing → [PROPOSED: Verifier rule enforcing immutability when state == FINALIZED]

### Test (`backend/verifiers/__tests__/StoryRecordStateVerifier.test.ts`) ✅

- [x] Reachability: pass StoryRecord with `state: 'FINALIZED'`, expect failure result.
- [x] TypeInvariant: assert verifier input type is `StoryRecord`, output type:
  ```ts
  { allowed: boolean; reason?: string }
  ```
- [x] ErrorConsistency: ensure failure reason equals `SESSION_ALREADY_FINALIZED`.

### Implementation ✅

- [x] Add rule in `StoryRecordStateVerifier`:
  ```ts
  if (record.status === 'FINALIZED') return { allowed: false, reason: 'SESSION_ALREADY_FINALIZED' }
  ```

---

## Step 5: Reject modification and preserve state ✅

**From path spec:**
- [x] Input: Validation failure + unchanged StoryRecord
- [x] Process: Service aborts flow, does NOT invoke DAO.update, maps to domain error
- [x] Output: Error response indicating session already finalized; StoryRecord unchanged
- [x] Error: If error mapping fails, fallback to generic conflict error

### Test (`backend/services/__tests__/SessionModificationService.reject.test.ts`) ✅

- [x] Reachability: when verifier returns disallowed, service returns `SessionErrors.SessionAlreadyFinalized`.
- [x] TypeInvariant: assert response shape:
  ```ts
  { status: 409; code: 'SESSION_ALREADY_FINALIZED' }
  ```
- [x] ErrorConsistency:
  - [x] Spy on `StoryRecordDAO.update` → assert NOT called.
  - [x] If error mapping throws, expect fallback `CONFLICT_GENERIC`.

### Implementation ✅

- [x] In `SessionModificationService`:
  - [x] If verifier fails → return error from `SessionErrors.SessionAlreadyFinalized`.
  - [x] Do not call DAO persistence methods.
  - [x] Wrap error mapping in try/catch for fallback.

---

## Terminal Condition ✅

### Integration Test (`server/__tests__/rejectFinalizedSession.integration.test.ts`) ✅

Flow:
1. [x] Seed DB with StoryRecord `{ status: 'FINALIZED' }`.
2. [x] Process modification with `ADD_VOICE` through handler → service → verifier.
3. [x] Assert:
   - [x] Error code = `SESSION_ALREADY_FINALIZED`, status = 409
   - [x] `DAO.updateDraft` NOT called
4. [x] Reload StoryRecord from DB → assert `status === 'FINALIZED'` and unchanged fields.

This proves:
- [x] Reachability: full path executed.
- [x] TypeInvariant: consistent types across layers.
- [x] ErrorConsistency: correct domain error + no persistence mutation.

---

## References
- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/309-reject-modifications-to-finalized-session.md
- Gate 1 Requirement: F-EPIC-SESSION (Acceptance Criteria #5)
- Gate 2 Tech Stack: Option 1 – Fastest Path
