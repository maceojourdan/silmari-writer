# reject-duplicate-session-initialization TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/311-reject-duplicate-session-initialization.md`

Tech Stack (Gate 2 – Option 1):
- Frontend/Backend: Next.js (App Router), TypeScript
- API: Next.js API Routes
- Validation: Zod
- Testing: Vitest (or Vitest) + Supertest
- DB: Supabase (Postgres)

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/311-reject-duplicate-session-initialization.md
```

Result (from verification_results_json):
- Result: ALL PROPERTIES PASSED
- States: 18 found, 9 distinct
- Exit code: 0

This guarantees that:
- The duplicate-session rejection path is reachable from the trigger.
- All step input/output types are consistent.
- All error branches resolve to valid error states.

The following TDD plan reproduces these guarantees at code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| api-m5g7 | endpoint | `backend/endpoints/sessionInitialization.ts` (Next.js route: `/api/session/init`) |
| api-n8k2 | request_handler | `backend/request_handlers/sessionInitializationHandler.ts` |
| db-h2s4 | service | `backend/services/sessionService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/sessionDao.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Session.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/sessionUniquenessVerifier.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/SessionErrors.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/sessionInit.ts` |

---

## Step 1: Receive session initialization request

**From path spec:**
- Input: HTTP request to endpoint (api-m5g7)
- Process: Accept and route request containing ResumeObject, JobObject, QuestionObject to backend service (db-h2s4)
- Output: Structured session initialization command passed to service layer
- Error: If payload malformed or missing required objects → validation error (db-l1c3)

### Test (`backend/__tests__/sessionInitialization.endpoint.test.ts`)

**Reachability**
- Send POST `/api/session/init` with valid `{ resume, job, question }`
- Assert handler calls service with structured command

**TypeInvariant**
- Assert parsed command matches TypeScript type `SessionInitCommand`
- Assert Zod schema validates input and narrows type

**ErrorConsistency**
- Send POST with missing `resume`
- Expect HTTP 400
- Expect error code from `SessionErrors.VALIDATION_ERROR`
- Response shape matches `frontend/api_contracts/sessionInit.ts`

### Implementation

- Define `SessionInitSchema` (Zod) requiring ResumeObject, JobObject, QuestionObject
- In `sessionInitializationHandler.ts`:
  - Parse request with Zod
  - On failure → throw `ValidationError` from `SessionErrors`
  - On success → build `SessionInitCommand`
  - Call `sessionService.initializeSession(command)`

---

## Step 2: Check for existing active session

**From path spec:**
- Input: SessionInitCommand + current session state via DAO (db-d3w8) from Session structure (db-f8n5)
- Process: Determine if active session exists
- Output: Boolean flag
- Error: If persistence failure → system error (db-l1c3)

### Test (`backend/__tests__/sessionService.checkActive.test.ts`)

**Reachability**
- Mock `sessionDao.getActiveSession()` to return active Session
- Call `initializeSession(command)`
- Assert DAO was called

**TypeInvariant**
- Ensure `getActiveSession()` returns `Session | null`
- Assert boolean flag derived correctly

**ErrorConsistency**
- Mock DAO to throw (e.g., DB connection error)
- Expect `SessionErrors.SYSTEM_ERROR`
- Assert no session creation attempted

### Implementation

- `Session` type in `Session.ts` with fields: id, status ('INIT' | 'FINALIZED'), resume, job, question
- In `sessionDao.ts`:
  - Implement `getActiveSession(): Promise<Session | null>` querying Supabase where status != FINALIZED
- In `sessionService.ts`:
  - Call DAO
  - Catch persistence exceptions → wrap in `SystemError`

---

## Step 3: Validate session uniqueness constraint

**From path spec:**
- Input: Active session existence flag + SessionInitCommand
- Process: Apply backend verifier (db-j6x9) prohibiting new session when one active
- Output: Validation result indicating rejection
- Error: If active session exists → generate `SESSION_ALREADY_ACTIVE`

### Test (`backend/__tests__/sessionUniquenessVerifier.test.ts`)

**Reachability**
- Given `activeSessionExists = true`
- Call `verifyUniqueness(flag)`

**TypeInvariant**
- Assert return type is `void` on pass
- Assert throws typed `DomainError` on failure

**ErrorConsistency**
- If flag = true
  - Expect thrown error with code `SESSION_ALREADY_ACTIVE`
  - Assert error matches definition in `SessionErrors`
- If flag = false
  - Expect no error

### Implementation

- In `SessionErrors.ts`:
  - Define `SESSION_ALREADY_ACTIVE` with code + message
- In `sessionUniquenessVerifier.ts`:
  - If `activeSessionExists` → throw `SessionErrors.SESSION_ALREADY_ACTIVE`
- In `sessionService.initializeSession()`:
  - Call verifier before creating session
  - Do not call `sessionDao.create()` if verifier throws

---

## Step 4: Return error response to client

**From path spec:**
- Input: Domain error `SESSION_ALREADY_ACTIVE`
- Process: Transform to standardized HTTP error via request handler (api-n8k2)
- Output: HTTP error response matching frontend contract (api-q7v1)
- Error: If transformation fails → generic internal error

### Test (`backend/__tests__/sessionInitialization.errorResponse.test.ts`)

**Reachability**
- Mock service to throw `SESSION_ALREADY_ACTIVE`
- Call endpoint
- Assert HTTP 409 (Conflict)

**TypeInvariant**
- Assert response JSON matches `SessionInitErrorResponse` type
- Fields: `{ error: { code: 'SESSION_ALREADY_ACTIVE', message: string } }`

**ErrorConsistency**
- Mock unexpected error in transformation layer
- Expect HTTP 500
- Error code = `SessionErrors.SYSTEM_ERROR`

### Implementation

- In `sessionInitializationHandler.ts`:
  - Catch `DomainError`
  - Map:
    - `SESSION_ALREADY_ACTIVE` → 409
    - `VALIDATION_ERROR` → 400
    - default → 500
- Ensure response shape matches `frontend/api_contracts/sessionInit.ts`

---

## Terminal Condition

### Integration Test (`backend/__tests__/rejectDuplicateSession.integration.test.ts`)

**Scenario:**
- Seed DB with active session (status = INIT)
- POST `/api/session/init` with valid ResumeObject, JobObject, QuestionObject

**Assertions:**
- HTTP 409 returned
- Error code `SESSION_ALREADY_ACTIVE`
- No new session row created in database
- Existing session unchanged

This proves:
- Reachability: full path from trigger to rejection exercised
- TypeInvariant: request → command → verifier → error → HTTP response types consistent
- ErrorConsistency: duplicate session always produces correct domain + HTTP error state

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/311-reject-duplicate-session-initialization.md`
- Gate 1 Requirement: `F-INIT-LOAD` (Acceptance Criteria #3)
- TLA+ Artifact: `RejectDuplicateSessionInitialization.tla`
