# initialize-new-session-with-provided-objects TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/310-initialize-new-session-with-provided-objects.md`

---

## Verification (Phase 0)
The TLA+ model for this path passed the following properties:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/310-initialize-new-session-with-provided-objects.md
```

Result (from verification_results_json):
```
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
```

This guarantees that every step is reachable, all step boundaries preserve types, and all defined error branches terminate in valid error states. The tests below directly assert those same properties at code level.

Tech Stack (Gate 2 – Option 1):
- Next.js (App Router) + TypeScript
- Next.js API Routes (Node runtime)
- Zod for validation
- Supabase (Postgres) for persistence
- Vitest or Vitest for backend tests

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|---------------|------------------------|
| api-m5g7 | endpoint | `frontend/src/app/api/sessions/initialize/route.ts` (Next.js API route `/api/sessions/initialize`) |
| api-n8k2 | request_handler | `frontend/src/server/request_handlers/InitializeSessionRequestHandler.ts` |
| db-h2s4 | service | `frontend/src/server/services/InitializeSessionService.ts` |
| db-d3w8 | data_access_object | `frontend/src/server/data_access_objects/InitializeSessionDAO.ts` |
| db-l1c3 | backend_error_definitions | `frontend/src/server/error_definitions/SessionErrors.ts` (SERVICE_ERROR added) |

Additional shared structures:
- `frontend/src/server/data_structures/SessionObjects.ts` (ResumeObject, JobObject, QuestionObject)
- `frontend/src/server/data_structures/InitializedSession.ts` (InitializedSession, request/response schemas)
- `frontend/src/api_contracts/initializeSession.ts` (frontend API contract)

---

## Step 1: Receive session initialization request

- [x] **Test** (`frontend/src/app/api/sessions/initialize/__tests__/route.test.ts`) — 8 tests passing
- [x] **Implementation** (`frontend/src/app/api/sessions/initialize/route.ts`)

**From path spec:**
- Input: HTTP request to api-m5g7 containing ResumeObject, JobObject, and QuestionObject.
- Process: Endpoint accepts request and forwards payload to request handler.
- Output: Structured session initialization payload forwarded to api-n8k2.
- Error: If malformed or missing required objects, return standardized error from db-l1c3.

### Test (`frontend/src/app/api/sessions/initialize/__tests__/route.test.ts`)

**Reachability**
- POST `/api/sessions/initialize` with valid JSON body.
- Assert request handler is invoked with structured payload.
- Assert 200 response returned (mock downstream success).

**TypeInvariant**
- Assert request body parsed into typed `ResumeObject`, `JobObject`, `QuestionObject` using Zod.
- Assert handler receives typed object (TypeScript compile-time + runtime Zod parse).

**ErrorConsistency**
- POST with missing `resume`.
- Assert HTTP 400.
- Assert error matches `SessionErrors.InvalidRequest()` shape from db-l1c3.

### Implementation (`frontend/src/app/api/sessions/initialize/route.ts`)
- Define Next.js POST handler.
- Parse body with Zod `InitializeSessionRequestSchema` for required objects.
- On failure → return `{ code: 'INVALID_REQUEST', message: ... }` with 400.
- On success → call `InitializeSessionRequestHandler.handle(payload)`.

---

## Step 2: Validate provided objects

- [x] **Test** (`frontend/src/server/request_handlers/__tests__/InitializeSessionRequestHandler.test.ts`) — 8 tests passing
- [x] **Implementation** (`frontend/src/server/request_handlers/InitializeSessionRequestHandler.ts`)

**From path spec:**
- Input: Structured payload from api-n8k2.
- Process: Validate ResumeObject, JobObject, QuestionObject against schemas and business rules.
- Output: Validated objects ready for session creation.
- Error: Validation error from db-l1c3.

### Test (`frontend/src/server/request_handlers/__tests__/InitializeSessionRequestHandler.test.ts`)

**Reachability**
- Call `handle(validPayload)`.
- Mock service to succeed.
- Assert validated objects passed to service.

**TypeInvariant**
- Assert returned value contains typed `InitializedSession` DTO.

**ErrorConsistency**
- Provide payload with invalid QuestionObject (e.g., empty text).
- Assert thrown/returned `SessionErrors.ValidationFailure`.
- Assert service is NOT called.

### Implementation (`frontend/src/server/request_handlers/InitializeSessionRequestHandler.ts`)
- Import shared Zod schemas (ResumeObjectSchema, JobObjectSchema, QuestionObjectSchema).
- Re-validate business rules (non-empty fields via Zod).
- On failure → throw `SessionErrors.ValidationFailure`.
- On success → call `InitializeSessionService.createSession(validatedObjects)`.

---

## Step 3: Create session entity

- [x] **Test** (`frontend/src/server/services/__tests__/InitializeSessionService.test.ts`) — 5 tests passing
- [x] **Implementation** (`frontend/src/server/services/InitializeSessionService.ts`)

**From path spec:**
- Input: Validated ResumeObject, JobObject, QuestionObject.
- Process: Construct new session entity embedding objects; set state = "initialized".
- Output: New session entity with state "initialized".
- Error: Service-level error from db-l1c3.

### Test (`frontend/src/server/services/__tests__/InitializeSessionService.test.ts`)

**Reachability**
- Call `createSession(validObjects)`.
- Assert returned session entity has:
  - Embedded ResumeObject, JobObject, QuestionObject
  - `state === "initialized"`

**TypeInvariant**
- Assert returned object conforms to `InitializedSession` type.

**ErrorConsistency**
- Simulate internal inconsistency (DAO throws non-session error).
- Assert `SessionErrors.ServiceError` thrown.

### Implementation (`frontend/src/server/services/InitializeSessionService.ts`)
- Construct session entity:
  ```ts
  {
    resume,
    job,
    question,
    state: "initialized",
    createdAt: new Date().toISOString()
  }
  ```
- Delegate to `InitializeSessionDAO.persist(session)`.
- Known `SessionError` → rethrow.
- Unknown errors → wrap in `SessionErrors.ServiceError(...)`.

---

## Step 4: Persist session to storage

- [x] **Test** (`frontend/src/server/data_access_objects/__tests__/InitializeSessionDAO.test.ts`) — 5 tests passing
- [x] **Implementation** (`frontend/src/server/data_access_objects/InitializeSessionDAO.ts`)

**From path spec:**
- Input: New session entity with state "initialized".
- Process: Delegate persistence to DAO.
- Output: Persisted session record with unique identifier.
- Error: Persistence error from db-l1c3.

### Test (`frontend/src/server/data_access_objects/__tests__/InitializeSessionDAO.test.ts`)

**Reachability**
- Call `persist(session)` with mocked Supabase client.
- Assert returned session has non-null `id`.

**TypeInvariant**
- Assert returned object matches `InitializedSession` type and preserves embedded objects.

**ErrorConsistency**
- Simulate DB failure (mock Supabase client to return error / throw).
- Assert `SessionErrors.PersistenceFailure` thrown.

### Implementation (`frontend/src/server/data_access_objects/InitializeSessionDAO.ts`)
- Use Supabase client.
- Insert into `sessions` table (JSONB columns for resume/job/question).
- On error → wrap in `SessionErrors.PersistenceFailure`.
- Return persisted record with generated UUID.

---

## Step 5: Return session initialization response

- [x] **Test** (`frontend/src/app/api/sessions/initialize/__tests__/route.response.test.ts`) — 5 tests passing
- [x] **Implementation** (in route.ts endpoint)

**From path spec:**
- Input: Persisted session record with unique identifier.
- Process: Format success response with session identifier, embedded objects, state "initialized".
- Output: HTTP success response.
- Error: Standardized error from db-l1c3.

### Test (`frontend/src/app/api/sessions/initialize/__tests__/route.response.test.ts`)

**Reachability**
- Mock handler + service + DAO to return persisted session.
- POST valid request.
- Assert HTTP 200.
- Assert response JSON contains:
  - `id`
  - `resume`, `job`, `question`
  - `state === "initialized"`

**TypeInvariant**
- Assert response matches `InitializeSessionResponseSchema` (frontend API contract).

**ErrorConsistency**
- Simulate formatting failure (undefined id).
- Assert `SERVICE_ERROR` response.

### Implementation
- In endpoint, after handler returns session:
  - Validate against `InitializeSessionResponseSchema`.
  - Return 200.
- On validation failure → return `SERVICE_ERROR`.
- All errors wrapped in structured JSON `{ code, message }`.

---

## Terminal Condition

- [x] **Integration Test** (`frontend/src/server/__tests__/initializeSession.integration.test.ts`) — 9 tests passing

### Integration Test (`frontend/src/server/__tests__/initializeSession.integration.test.ts`)

Exercise full path:
- POST `/api/sessions/initialize` with valid ResumeObject, JobObject, QuestionObject.
- Assert:
  - 200 response
  - `state === "initialized"`
  - DAO.persist called (simulates DB row exists)
  - Embedded objects match input exactly

This proves:
- Reachability: Trigger exercises entire chain.
- TypeInvariant: Objects preserved end-to-end.
- ErrorConsistency: All error branches tested independently above.

---

## Additional Artifacts

- [x] **Data Structures** (`frontend/src/server/data_structures/InitializedSession.ts`)
- [x] **Error Definitions** (`frontend/src/server/error_definitions/SessionErrors.ts` — SERVICE_ERROR added)
- [x] **API Contract** (`frontend/src/api_contracts/initializeSession.ts`)

---

## Test Summary

| Layer | Test File | Tests |
|-------|-----------|-------|
| Endpoint (Step 1) | `route.test.ts` | 8 |
| Request Handler (Step 2) | `InitializeSessionRequestHandler.test.ts` | 8 |
| Service (Step 3) | `InitializeSessionService.test.ts` | 5 |
| DAO (Step 4) | `InitializeSessionDAO.test.ts` | 5 |
| Response (Step 5) | `route.response.test.ts` | 5 |
| Integration (Terminal) | `initializeSession.integration.test.ts` | 9 |
| **Total** | **6 files** | **40** |

---

## References
- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/310-initialize-new-session-with-provided-objects.md`
- Gate 1: `F-INIT-LOAD`
- Gate 2: Option 1 – Fastest Path (Next.js + Supabase)
