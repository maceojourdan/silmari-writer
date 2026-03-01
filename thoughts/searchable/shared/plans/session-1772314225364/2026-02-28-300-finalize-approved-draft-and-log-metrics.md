# finalize-approved-draft-and-log-metrics TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/300-finalize-approved-draft-and-log-metrics.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/300-finalize-approved-draft-and-log-metrics.md
```

Verifier output:
```
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
```

This guarantees at the model level:
- Every step from FINALIZE trigger to terminal state is reachable.
- All step input/output types are consistent.
- Every defined error branch results in a valid error state.

This TDD plan reproduces those guarantees at the code level using Next.js (App Router), TypeScript, Zod, Supabase, and Vitest.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/finalize.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/FinalizeRequestHandler.ts` |
| db-b7r2 | processor | `backend/processors/FinalizeProcessor.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/DraftDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Draft.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/FinalizeErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |
| cfg-p4b8 | shared_logging | `shared/logging/index.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |

Test runner: Vitest

---

## Step 1: Invoke Finalize Endpoint ✅

**From path spec:**
- Input: User action FINALIZE with approved draft identifier via frontend API contract (api-q7v1)
- Process: Frontend sends FINALIZE request to backend including draftId and user context
- Output: HTTP request delivered to backend endpoint
- Error: Malformed request or network failure → shared_error_definitions (cfg-j9w2)

### Test (`frontend/api_contracts/__tests__/finalize.test.ts`)

- Reachability:
  - Call `finalizeDraft({ draftId, userId })`
  - Assert POST to `/api/finalize` occurs
- TypeInvariant:
  - Zod schema validates `{ draftId: string, userId: string }`
  - Response type matches `FinalizeResponse`
- ErrorConsistency:
  - Call with `{ draftId: "" }`
  - Expect `SharedErrors.MalformedRequest`

### Implementation (`frontend/api_contracts/finalize.ts`)

- Define `FinalizeRequestSchema` (Zod)
- Define `FinalizeResponseSchema`
- Export `finalizeDraft()` using `fetch`
- Map validation/network errors to `SharedErrors`

---

## Step 2: Validate Draft Approval State ✅

**From path spec:**
- Input: FINALIZE request handled by request handler and delegated to processor with draft entity via DAO
- Process: Retrieve draft and verify state = APPROVED
- Output: Validated approved draft
- Error: Not found or not APPROVED → backend_error_definitions (db-l1c3)

### Test (`backend/processors/__tests__/FinalizeProcessor.validate.test.ts`)

- Reachability:
  - Mock DAO returning draft `{ status: "APPROVED" }`
  - Call `validateApprovedDraft(draftId)`
  - Expect returned Draft
- TypeInvariant:
  - Assert returned object matches `Draft` type
- ErrorConsistency:
  - DAO returns null → expect `FinalizeErrors.DraftNotFound`
  - DAO returns `{ status: "DRAFT" }` → expect `FinalizeErrors.InvalidDraftState`

### Implementation

**Draft structure** (`backend/data_structures/Draft.ts`):
- Fields: id, status ("DRAFT" | "APPROVED" | "FINALIZED"), timestamps, interactionData

**DAO** (`backend/data_access_objects/DraftDAO.ts`):
- `getDraftById(id)`

**Processor** (`backend/processors/FinalizeProcessor.ts`):
- `validateApprovedDraft(draftId)`
- Throw `FinalizeErrors.*` if invalid

---

## Step 3: Generate Exportable Answer Artifact ✅

**From path spec:**
- Input: Approved draft content and metadata
- Process: Transform into exportable format and mark FINALIZED
- Output: Export artifact + persisted status FINALIZED
- Error: Transformation/persistence failure → backend_error_definitions, logged via backend_logging; draft remains APPROVED

### Test (`backend/processors/__tests__/FinalizeProcessor.export.test.ts`)

- Reachability:
  - Mock draft APPROVED
  - Call `finalizeDraft(draftId)`
  - Expect returned `{ artifact, status: "FINALIZED" }`
- TypeInvariant:
  - Artifact matches `ExportArtifact` type
  - DAO `updateStatus` called with "FINALIZED"
- ErrorConsistency:
  - Simulate DAO failure on update
  - Expect `FinalizeErrors.PersistenceFailure`
  - Verify draft status remains "APPROVED"
  - Verify `backend_logging.error` called

### Implementation

In `FinalizeProcessor.ts`:
- `transformToArtifact(draft)`
- `finalizeDraft(draftId)`:
  1. validateApprovedDraft
  2. transform
  3. DAO.updateStatus(id, "FINALIZED")
- Wrap in try/catch
- Log via `backend/logging`

---

## Step 4: Compute and Log Metrics ✅

**From path spec:**
- Input: Finalized draft timestamps and interaction data
- Process: Compute time-to-draft, confirmation rate, signal density; log via shared_logging and/or persist
- Output: Metrics log entries
- Error: Metrics failure logged; FINALIZED state remains valid

### Test (`backend/processors/__tests__/FinalizeProcessor.metrics.test.ts`)

- Reachability:
  - Mock finalized draft with timestamps
  - Call `computeAndLogMetrics(draft)`
  - Expect `shared_logging.info` called with metrics
- TypeInvariant:
  - Metrics object matches `{ timeToDraft: number, confirmationRate: number, signalDensity: number }`
- ErrorConsistency:
  - Simulate computation error
  - Expect error logged via `shared_logging.error`
  - No exception thrown to caller
  - Draft status remains FINALIZED

### Implementation

In `FinalizeProcessor.ts`:
- `computeMetrics(draft)` pure function
- `computeAndLogMetrics(draft)`:
  - try compute
  - log via `shared/logging`
  - swallow/log errors

Optional: `DraftDAO.insertMetrics(draftId, metrics)`

---

## Step 5: Return Export Response to User ✅

**From path spec:**
- Input: Export artifact + FINALIZED status
- Process: Request handler constructs success response
- Output: User receives export payload + confirmation of metrics logging
- Error: Response construction failure → backend_error_definitions; user informed retry may be required

### Test (`backend/request_handlers/__tests__/FinalizeRequestHandler.test.ts`)

- Reachability:
  - Mock processor returning artifact + FINALIZED
  - Call handler with valid request
  - Expect HTTP 200 with `{ artifact, finalized: true, metricsLogged: true }`
- TypeInvariant:
  - Response matches `FinalizeResponse` schema
- ErrorConsistency:
  - Mock processor throwing `FinalizeErrors.*`
  - Expect mapped HTTP error response
  - Logged via backend_logging

### Implementation

`backend/request_handlers/FinalizeRequestHandler.ts`:
- Parse body
- Call `FinalizeProcessor.finalizeDraft()`
- Call `computeAndLogMetrics()`
- Return JSON response
- Catch and map errors

`app/api/finalize/route.ts` (Next.js API route):
- Delegates to request handler

---

## Terminal Condition ✅

### Integration Test (`backend/__tests__/Finalize.integration.test.ts`)

- Seed DB with draft in APPROVED state
- Perform POST `/api/finalize`
- Assert:
  - Response 200
  - Draft status in DB = FINALIZED
  - Export artifact present
  - Metrics log entry recorded

This proves:
- Full path reachable from trigger to terminal state
- Types consistent across API → handler → processor → DAO
- Error branches isolated and do not corrupt FINALIZED state

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/300-finalize-approved-draft-and-log-metrics.md`
- Gate 1: `F-FINALIZE-EXPORT`, `NF-KPI-LOGGING`
- TLA+ spec: `FinalizeApprovedDraftAndLogMetrics.tla`
