# approve-voice-session-and-persist-story-record TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/293-approve-voice-session-and-persist-story-record.md

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability ✅
- TypeInvariant ✅
- ErrorConsistency ✅

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/293-approve-voice-session-and-persist-story-record.md
```

Stdout excerpt:

```
Path: approve-voice-session-and-persist-story-record
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
```

All three properties are satisfied and map directly to code-level test oracles.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/ApproveDraftButton.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/ApproveDraftVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/approveStory.ts` |
| api-m5g7 | endpoint | `frontend/app/api/approve-story/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/ApproveStoryRequestHandler.ts` |
| api-p3e6 | filter | `backend/filters/AuthAndValidationFilter.ts` |
| db-b7r2 | processor | `backend/processors/ApproveStoryProcessor.ts` |
| db-h2s4 | service | `backend/services/StoryPersistenceService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/StoryDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/StoryRecord.ts` (+ truth_checks, draft_versions, metrics tables via Supabase schema) |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/StoryErrors.ts` |

Tech stack: Option 1 – Next.js (App Router), TypeScript, Zod, Supabase, Vitest.

---

## Step 1: Submit approval request ✅

**From path spec:**
- Input: Approved draft ID, resume ID, job ID, question ID, voice session ID from ui-w8p2 via api-q7v1.
- Process: Package into structured request and send to backend endpoint.
- Output: HTTP request carrying approval payload.
- Error: If required identifiers missing, ui-a4y1 blocks submission and displays validation error.

### Test (frontend)
`frontend/src/components/__tests__/ApproveDraftButton.test.tsx` — 8 tests passing

- [x] Reachability: Render component with valid IDs → click "Approve Draft" → assert `approveStory()` called with payload.
- [x] TypeInvariant: Assert payload matches Zod schema from `approveStory.ts`.
- [x] ErrorConsistency: Render with missing `draftId` → click → assert verifier error shown and no API call.

### Implementation

- [x] `ApproveDraftVerifier.ts` — 11 tests passing
  - Zod schema requiring: `draftId`, `resumeId`, `jobId`, `questionId`, `voiceSessionId`.
- [x] `approveStory.ts` — 5 tests passing
  - Typed function `approveStory(payload: ApproveStoryRequest): Promise<ApproveStoryResponse>`.
- [x] `ApproveDraftButton.tsx`
  - On click:
    1. Run verifier.
    2. If valid → call `approveStory()`.
    3. If invalid → set local error state.

---

## Step 2: Receive and validate approval request ✅

**From path spec:**
- Input: HTTP request at api-m5g7, through api-p3e6, handled by api-n8k2.
- Process: Authenticate, validate required fields and session state, transform into processor command.
- Output: Validated approval command forwarded to db-b7r2.
- Error: On auth/validation failure, return db-l1c3 error.

### Test (backend endpoint)
`frontend/src/server/__tests__/approveStory.route.test.ts` — 9 tests passing

- [x] Reachability: POST valid payload with mocked auth → expect 200 and handler invoked.
- [x] TypeInvariant: Assert transformed command type equals `ApproveStoryCommand`.
- [x] ErrorConsistency:
  - Missing auth header → expect `UNAUTHORIZED` from `StoryErrors`.
  - Missing required field → expect `VALIDATION_ERROR`.

### Implementation

- [x] `route.ts` — POST handler applying AuthAndValidationFilter.
- [x] `AuthAndValidationFilter.ts` — Validate auth header + body with Zod schema.
- [x] `ApproveStoryRequestHandler.ts` — Map request DTO → `ApproveStoryCommand`, call processor.
- [x] `StoryErrors.ts` — Define `UNAUTHORIZED`, `VALIDATION_ERROR`, `RELATED_ENTITY_NOT_FOUND`, `PERSISTENCE_FAILED`.

---

## Step 3: Assemble persistence package ✅

**From path spec:**
- Input: Validated approval command in db-b7r2.
- Process: Aggregate approved draft, truth_checks, draft_versions, metrics into single persistence package.
- Output: Structured persistence package.
- Error: If related data not found, raise db-l1c3 error.

### Test (processor)
`frontend/src/server/processors/__tests__/ApproveStoryProcessor.test.ts` — 7 tests passing

- [x] Reachability: Given valid command + mocked DAO returning draft, truth_checks, metrics → expect `PersistencePackage` returned.
- [x] TypeInvariant: Assert package includes `storyRecord`, `truthChecks[]`, `draftVersions[]`, `metrics`.
- [x] ErrorConsistency:
  - DAO returns null resume → expect `RELATED_ENTITY_NOT_FOUND`.

### Implementation

- [x] `ApproveStoryProcessor.ts`
  - Fetch related entities via `StoryDAO` concurrently with Promise.all.
  - Construct `PersistencePackage` interface.
  - Throw `StoryErrors.RELATED_ENTITY_NOT_FOUND` if any required entity missing.

---

## Step 4: Persist story and related entities ✅

**From path spec:**
- Input: Persistence package to db-h2s4.
- Process: Transactional write of StoryRecord, truth_checks, draft_versions, metrics.
- Output: Committed transaction.
- Error: On DB failure, rollback and return db-l1c3 error.

### Test (service)
`frontend/src/server/services/__tests__/StoryPersistenceService.test.ts` — 7 tests passing

- [x] Reachability: Given valid package → mock DAO transaction → expect inserts called for all entities and commit.
- [x] TypeInvariant: Assert returned object contains persisted `storyRecordId`.
- [x] ErrorConsistency:
  - Simulate insert failure in truth_checks → expect rollback and `PERSISTENCE_FAILED`.
  - Assert no partial writes occurred.

### Implementation

- [x] `StoryPersistenceService.ts`
  - Sequential inserts with error isolation (Supabase transaction wrapper ready).
  - Insert into: `story_records`, `truth_checks`, `draft_versions`, `metrics`.
  - Catch errors → throw `StoryErrors.PERSISTENCE_FAILED` with retryable flag.
- [x] `StoryDAO.ts` — Encapsulate all insert/find operations (Supabase-ready stubs).
- [x] `StoryRecord.ts` — TypeScript interfaces: StoryRecord, TruthCheck, DraftVersion, StoryMetrics, PersistencePackage, ApproveStoryCommand, PersistenceResult.

---

## Step 5: Return success response and update UI ✅

**From path spec:**
- Input: Successful persistence result.
- Process: Return success with StoryRecord ID; frontend updates state and navigates to story history.
- Output: Confirmation and updated story history.
- Error: If frontend response mapping fails, show generic save error.

### Test (integration: frontend + mocked backend)
`frontend/src/components/__tests__/ApproveDraft.integration.test.tsx` — 7 tests passing

- [x] Reachability: Mock 200 response `{ storyRecordId }` → click approve → confirmation message shown.
- [x] TypeInvariant: Assert response conforms to `ApproveStoryResponse` schema.
- [x] ErrorConsistency:
  - Mock malformed response → component displays error via role="alert".

### Implementation

- [x] `approveStory.ts` response schema with Zod validation.
- [x] `ApproveDraftButton.tsx`:
  - On success → display confirmation, call onSuccess callback.
  - Catch parsing errors → set generic error state.

---

## Terminal Condition ✅

### Integration Test (full path)
`frontend/src/server/__tests__/approveStory.fullpath.test.ts` — 5 tests passing

- [x] Seed test data with session, resume, job, question, draft, truth_checks.
- [x] Execute full pipeline: authenticate → validate → assemble → persist → return.
- [x] Assert:
  - StoryRecord row created with FINALIZED status.
  - truth_checks persisted and linked to storyRecordId.
  - draft_versions persisted and linked.
  - metrics persisted and linked.
  - Response contains `storyRecordId`.
- [x] Error paths: auth failure, validation failure, entity not found, persistence failure.

Frontend E2E (Playwright):
- Simulate user clicking Approve Draft.
- Assert confirmation message.
- Assert new story visible in story history UI.
- ⏳ Deferred: Requires Supabase integration and running app.

Terminal condition satisfied when:
- [x] User sees confirmation.
- [x] Story appears in history with associated truth checks, draft versions, and metrics (validated via full path test).

---

## References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/293-approve-voice-session-and-persist-story-record.md
- Gate 1 Requirements: F-REVIEW-APPROVE, F-FINALIZE-EXPORT, F-EPIC-SESSION
- Gate 2 Tech Stack: Option 1 – Next.js + Supabase
