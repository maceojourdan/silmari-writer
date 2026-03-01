# reject-session-initialization-when-required-objects-missing-or-invalid TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/312-reject-session-initialization-when-required-objects-missing-or-invalid.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/312-reject-session-initialization-when-required-objects-missing-or-invalid.md
```

Verification result:
- Result: ALL PROPERTIES PASSED
- States: 22 found, 11 distinct, depth 0
- Exit code: 0

This plan mirrors those three properties at the code level.

---

## Tech Stack (Gate 2 – Option 1)
- Backend: Next.js API Routes (Node.js, TypeScript)
- Validation: Zod
- Testing: Vitest (or Vitest) + Supertest
- Database: Supabase (Postgres)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| api-m5g7 | endpoint | `backend/endpoints/sessionInit.ts` (Next.js API route `/api/session/init`) |
| api-n8k2 | request_handler | `backend/request_handlers/SessionInitHandler.ts` |
| db-h2s4 | service | `backend/services/SessionInitService.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/SessionObjectVerifier.ts` |
| cfg-g1u4 | shared_verifier | `shared/verifiers/ObjectSchemaVerifier.ts` (Zod schemas) |
| db-d3w8 | data_access_object | `backend/data_access_objects/SessionDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Session.ts` (sessions table schema) |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/SessionErrors.ts` |

---

## Step 1: Receive session initialization request

- [x] **Implemented**

**From path spec:**
- Input: HTTP request containing ResumeObject, JobObject, QuestionObject
- Process: Endpoint parses and forwards structured payload to request handler
- Output: Structured request data delivered to request handler
- Error: If parsing fails, return standardized validation error (db-l1c3)

### Test (`tests/integration/sessionInit.endpoint.test.ts`)

- [x] **Reachability**
- Send valid JSON body to `/api/session/init`
- Assert handler is invoked (mock `SessionInitHandler.handle`)
- Assert 4xx not returned at this stage

- [x] **TypeInvariant**
- Assert parsed body matches `SessionInitRequest` TypeScript type
- Assert handler receives `{ resume: ResumeObject; job: JobObject; question: QuestionObject }`

- [x] **ErrorConsistency**
- Send malformed JSON (e.g., invalid body)
- Expect HTTP 400
- Expect error code from `SessionErrors.INVALID_REQUEST_FORMAT`
- Assert handler not called

### Implementation (`backend/endpoints/sessionInit.ts`)

- [x] Define `SessionInitRequestSchema` (Zod) in shared verifier
- [x] Parse `req.body` via Zod
- [x] On failure: Return `SessionErrors.INVALID_REQUEST_FORMAT`
- [x] On success: Call `SessionInitHandler.handle(parsedData)`

---

## Step 2: Delegate to session service

- [x] **Implemented**

**From path spec:**
- Input: Structured session initialization data
- Process: Handler invokes service
- Output: Service-level command sent to service
- Error: If contract violated, return service invocation error

### Test (`tests/unit/SessionInitHandler.test.ts`)

- [x] **Reachability**
- Mock `SessionInitService.initialize`
- Call `handle(validInput)`
- Assert service called with same structured input

- [x] **TypeInvariant**
- Assert handler passes typed object (no mutation, correct keys)

- [x] **ErrorConsistency**
- Mock service to throw `ServiceContractError`
- Expect handler to map to `SessionErrors.SERVICE_INVOCATION_FAILED`

### Implementation (`backend/request_handlers/SessionInitHandler.ts`)

- [x] Export `handle(input: SessionInitRequest)`
- [x] Call `SessionInitService.initialize(input)`
- [x] Catch contract errors → map using `SessionErrors.SERVICE_INVOCATION_FAILED`

---

## Step 3: Validate required domain objects

- [x] **Implemented**

**From path spec:**
- Input: ResumeObject, JobObject, QuestionObject
- Process: Validate presence and structure using backend_verifier and shared_verifier
- Output: Validation failure with object-level details
- Error: If missing/invalid → construct validation error and halt

### Test (`tests/unit/SessionInitService.validation.test.ts`)

- [x] **Reachability**
- Call `initialize()` with one invalid object
- Assert validation logic executes

- [x] **TypeInvariant**
- Provide structurally valid objects → expect validation result type `ValidationSuccess | ValidationFailure`

- [x] **ErrorConsistency**
- Cases:
  - Missing resume
  - Invalid job structure
  - Missing question
- Expect:
  - `SessionErrors.MISSING_REQUIRED_OBJECT`
  - Error payload includes specific object names
- Assert `SessionDAO.create` NOT called (mocked)

### Implementation (`backend/services/SessionInitService.ts`)

- [x] Use:
  - `ObjectSchemaVerifier` (Zod schemas)
  - `SessionObjectVerifier` for semantic rules
- [x] Aggregate errors into array
- [x] If any errors:
  - Return `SessionErrors.VALIDATION_FAILED` with object-level detail
  - Do not call DAO

---

## Step 4: Prevent session persistence

- [x] **Implemented**

**From path spec:**
- Input: Validation failure result
- Process: Short-circuit workflow; ensure DAO not invoked
- Output: Confirm no new session record
- Error: If persistence attempted → abort + internal error

### Test (`tests/unit/SessionInitService.persistence.test.ts`)

- [x] **Reachability**
- Trigger validation failure
- Assert `SessionDAO.create` not called

- [x] **TypeInvariant**
- Ensure no `Session` entity instance created

- [x] **ErrorConsistency**
- Simulate DAO accidentally invoked after validation failure
- Expect service throws `SessionErrors.INTERNAL_PERSISTENCE_VIOLATION`

### Implementation

- [x] In `initialize()`:
  - Perform validation first
  - If failure → return early
  - DAO call exists strictly after validation success branch
- [x] Add guard to prevent DAO invocation when validationErrors.length > 0

---

## Step 5: Return validation error response

- [x] **Implemented**

**From path spec:**
- Input: Validation error object
- Process: Map to HTTP error response
- Output: HTTP error specifying missing/invalid objects
- Error: If mapping fails → generic user-visible error

### Test (`tests/integration/sessionInit.validationResponse.test.ts`)

- [x] **Reachability**
- Send request missing ResumeObject
- Expect HTTP 400
- Response body contains object-level error detail

- [x] **TypeInvariant**
- Assert response matches `ValidationErrorResponse` type

- [x] **ErrorConsistency**
- Mock handler error mapping failure
- Expect generic error `SessionErrors.GENERIC_USER_ERROR`
- No stack trace exposed

### Implementation

- [x] In endpoint:
  - Catch service-level `ValidationError`
  - Map to HTTP 400 with structured JSON
- [x] Fallback catch-all → return `GENERIC_USER_ERROR`

---

## Terminal Condition

- [x] **Implemented**

### Integration Test (`tests/integration/sessionInit.fullFailureFlow.test.ts`)

- [x] Exercise full path from trigger:
- Send request with missing JobObject
- Assert:
  - HTTP 400 returned
  - Error message explicitly identifies "JobObject"
  - No record inserted in `sessions` table (query Supabase test DB)

- [x] Assertions:
- Reachability: Full endpoint → handler → service → error response
- TypeInvariant: All boundaries enforce typed schemas
- ErrorConsistency: Validation error always produced; no session created

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/312-reject-session-initialization-when-required-objects-missing-or-invalid.md`
- Gate 1 Requirement: `F-INIT-LOAD` (acceptance criterion 4)
- Gate 2 Tech Stack: Option 1 – Fastest Path (All Off-the-Shelf, Managed-First)
