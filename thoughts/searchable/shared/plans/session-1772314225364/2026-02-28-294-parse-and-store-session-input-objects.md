# parse-and-store-session-input-objects TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/294-parse-and-store-session-input-objects.md`

---

## Verification (Phase 0)
The TLA+ model for this path passed: **Reachability**, **TypeInvariant**, **ErrorConsistency**.

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/294-parse-and-store-session-input-objects.md
```

Result:
```
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
Properties: Reachability, TypeInvariant, ErrorConsistency
```

This TDD plan mirrors those guarantees at code level:
- Reachability → Each step is directly invocable from the previous step's output.
- TypeInvariant → Zod schemas + TypeScript types asserted at boundaries.
- ErrorConsistency → Each defined error path returns standardized error objects.

Tech Stack (Gate 2 – Option 1):
- Next.js (App Router) + TypeScript
- API Routes (Node runtime)
- Zod for validation
- Supabase (Postgres) for persistence
- Vitest for unit tests

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-v3n6 | module | `frontend/modules/session/SessionInitModule.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/src/verifiers/SessionInitVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/src/api_contracts/initSession.ts` |
| api-m5g7 | endpoint | `frontend/src/app/api/session/init/route.ts` |
| api-n8k2 | request_handler | `frontend/src/server/request_handlers/InitSessionRequestHandler.ts` |
| db-b7r2 | processor | `frontend/src/server/processors/SessionInputProcessor.ts` |
| cfg-h5v9 | transformer | `frontend/src/server/transformers/SessionInputTransformer.ts` |
| cfg-d2q3 | common_structure | `frontend/src/server/data_structures/SessionObjects.ts` |
| cfg-g1u4 | shared_verifier | `frontend/src/server/verifiers/SessionObjectVerifier.ts` |
| db-h2s4 | service | `frontend/src/server/services/SessionInitService.ts` |
| db-d3w8 | data_access_object | `frontend/src/server/data_access_objects/SessionInitDAO.ts` |
| db-f8n5 | data_structure | Supabase tables: `resumes`, `jobs`, `questions`, `sessions` |
| db-l1c3 | backend_error_definitions | `frontend/src/server/error_definitions/SessionErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `frontend/src/server/error_definitions/GenericErrors.ts` |
| cfg-q9c5 | backend_logging | `frontend/src/server/logging/logger.ts` |

---

## Step 1: Submit session initialization request

**From path spec:**
- Input: Resume content, job link/text, question text (ui-v3n6) validated by ui-a4y1
- Process: Package into request conforming to api-q7v1 and send to api-m5g7
- Output: HTTP request following frontend API contract
- Error: Client-side validation errors prevent submission

### Test (`frontend/verifiers/SessionInitVerifier.test.ts`)

- [x] Reachability: call `validateSessionInitInput(validInput)` → expect `{ success: true }`
- [x] TypeInvariant: assert parsed result matches `InitSessionRequestSchema` (Zod)
- [x] ErrorConsistency: missing resume → expect `{ success: false, errors: { resume: ... }}`

### Implementation

- [x] Define `InitSessionRequestSchema` in `frontend/api_contracts/initSession.ts` using Zod.
- [x] Implement `validateSessionInitInput` in `SessionInitVerifier.ts`.
- [ ] In `SessionInitModule.tsx`, block submission if validation fails and render error messages.

---

## Step 2: Handle session initialization endpoint

**From path spec:**
- Input: HTTP request (api-m5g7)
- Process: Endpoint delegates to request handler (api-n8k2) → processor (db-b7r2)
- Output: Invocation of request handler with raw payload
- Error: Malformed request → standardized backend error (db-l1c3)

### Test (`app/api/session/init/route.test.ts`)

- [x] Reachability: POST valid body → handler invoked → 200 response stub
- [x] TypeInvariant: invalid shape → 400 with `SessionErrors.InvalidRequest`
- [x] ErrorConsistency: missing required field → structured JSON error `{ code, message }`

### Implementation

- [x] In `route.ts`, parse JSON and validate with shared `InitSessionRequestSchema`.
- [x] On failure → return `SessionErrors.InvalidRequest` (HTTP 400).
- [x] On success → call `InitSessionRequestHandler.handle(payload)`.

---

## Step 3: Parse raw inputs into structured objects

**From path spec:**
- Input: Raw resume, job, question (processor db-b7r2)
- Process: Use transformer (cfg-h5v9) → produce ResumeObject, JobObject, QuestionObject (cfg-d2q3) → validate via shared verifier (cfg-g1u4)
- Output: Validated in-memory objects
- Error: Parsing failure → backend error; validation failure → structured error response

### Test (`backend/processors/SessionInputProcessor.test.ts`)

- [x] Reachability: call `process(rawInput)` → returns `{ resume, job, question }`
- [x] TypeInvariant: each matches Zod schema from `SessionObjects.ts`
- [x] ErrorConsistency:
  - [x] Transformer throws → expect `SessionErrors.ParseFailure`
  - [x] Verifier fails → expect `SessionErrors.ValidationFailure`

### Implementation

- [x] Define `ResumeObjectSchema`, `JobObjectSchema`, `QuestionObjectSchema` in `SessionObjects.ts`.
- [x] Implement `SessionInputTransformer.transform(raw)`.
- [x] Implement `SessionObjectVerifier.validate(obj)`.
- [x] `SessionInputProcessor.process()` composes transformer + verifier and maps errors to `SessionErrors`.

---

## Step 4: Persist structured objects

**From path spec:**
- Input: Validated objects
- Process: Service (db-h2s4) calls DAO (db-d3w8) → store in tables (db-f8n5)
- Output: Persisted records with generated IDs
- Error: DB failure → standardized persistence error

### Test (`backend/services/SessionInitService.test.ts`)

- [x] Reachability: valid objects → returns `{ sessionId, resumeId, jobId, questionId }`
- [x] TypeInvariant: IDs are UUID strings
- [x] ErrorConsistency: DAO throws → expect `SessionErrors.PersistenceFailure`

### Implementation

- [ ] Create Supabase tables: `resumes`, `jobs`, `questions`, `sessions`.
- [x] Implement `SessionInitDAO` with mockable insert methods (stub until Supabase wiring).
- [x] Implement `SessionInitService.initialize()` orchestrating DAO and returning IDs.
- [x] Map DB errors to `SessionErrors.PersistenceFailure`.

---

## Step 5: Return session start confirmation

**From path spec:**
- Input: Persistence result with IDs
- Process: Request handler constructs success response → endpoint returns to frontend
- Output: Frontend receives success and displays confirmation
- Error: Unexpected formatting → log (cfg-q9c5) and return generic error (cfg-j9w2)

### Test (`backend/request_handlers/InitSessionRequestHandler.test.ts`)

- [x] Reachability: service returns IDs → handler returns `{ sessionId, resumeId, jobId, questionId }`
- [x] TypeInvariant: response matches `InitSessionResponseSchema`
- [x] ErrorConsistency: unexpected exception → logs error and returns `GenericErrors.InternalError`

### Implementation

- [x] Define `InitSessionResponseSchema`.
- [x] Implement handler composing processor + service.
- [x] Wrap in try/catch → log via `logger.error()` and return `GenericErrors.InternalError`.
- [ ] Frontend module updates UI to show confirmation state.

---

## Terminal Condition

### Integration Test (`server/__tests__/initSession.integration.test.ts`)

- [x] Trigger: POST valid resume, job, question
- [x] Assert:
  - [x] 200 response with session + object IDs
  - [x] DAO receives structured objects with correct fields
  - [x] Error paths return standardized error objects
- [x] Assert error paths:
  - [x] Invalid input rejected at validation layer
  - [x] DAO failure → PERSISTENCE_FAILURE
  - [x] Whitespace-only input → PARSE_FAILURE

This proves:
- Reachability: Trigger → Endpoint → Handler → Processor → Service → DAO → Response
- TypeInvariant: All boundary schemas validated via Zod
- ErrorConsistency: All defined error branches return standardized error objects

---

## Implementation Notes

**Remaining work (future paths):**
- [ ] `SessionInitModule.tsx` UI component (frontend module - ui-v3n6)
- [ ] Supabase table creation (db-f8n5) — DDL migrations
- [ ] Wire `SessionInitDAO` to actual Supabase client

**Test Results (2026-03-01):**
- 93 total tests passing (13 test files)
- TypeScript compiles cleanly (`tsc --noEmit`)
- All TLA+ properties verified at code level

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/294-parse-and-store-session-input-objects.md`
- Gate 1: F-INIT-LOAD
- Gate 2: Option 1 – Next.js + Supabase
