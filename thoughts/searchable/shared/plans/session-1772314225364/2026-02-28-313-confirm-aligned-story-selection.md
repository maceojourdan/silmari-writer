# confirm-aligned-story-selection TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/313-confirm-aligned-story-selection.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/313-confirm-aligned-story-selection.md
```

Stdout:

```
Path: confirm-aligned-story-selection
TLA+ spec: .../ConfirmAlignedStorySelection.tla
TLC config: .../ConfirmAlignedStorySelection.cfg
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
```

All three properties were verified by TLC with exit code 0.

---

## Tech Stack (Gate 2 – Option 1)

- Frontend: Next.js (App Router), React, TypeScript, Tailwind
- Backend: Next.js API Routes, TypeScript, Zod
- Database: Supabase (Postgres)
- Testing:
  - Backend: Vitest
  - Frontend: Vitest + React Testing Library
  - Integration: Supertest (API routes)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| db-f8n5 | data_structure | `backend/data_structures/Story.ts`, `Question.ts`, `JobRequirement.ts` (Supabase tables) |
| db-d3w8 | data_access_object | `backend/data_access_objects/StoryDAO.ts` |
| db-h2s4 | service | `backend/services/ConfirmStoryService.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/StoryAlignmentVerifier.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/DomainErrors.ts` |
| api-m5g7 | endpoint | `app/api/story/confirm/route.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/confirmStory.ts` |
| ui-v3n6 | module | `frontend/modules/orient-story/OrientStoryModule.tsx` |
| ui-w8p2 | component | `frontend/components/StorySelection.tsx` |
| ui-y5t3 | data_loader | `frontend/data_loaders/loadOrientStoryData.ts` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/StorySelectionVerifier.ts` |

---

## Step 1: Render question requirements and stories ✅

**From path spec:**
- [x] Input: Active question + job requirements + stories from db-f8n5 via api-m5g7 → ui-y5t3
- [x] Process: Retrieve and present in single selection interface
- [x] Output: UI displays question, job requirements, stories
- [x] Error: Retrieval failure → db-l1c3 error → UI error state with retry

### Test (Frontend) ✅
`frontend/modules/orient-story/__tests__/render-orient-story.test.tsx` — **12 tests passing**

- [x] Reachability:
  - Mock `loadOrientStoryData()` to return { question, jobRequirements, stories }
  - Render `OrientStoryModule`
  - Assert question text and story list visible
- [x] TypeInvariant:
  - Assert returned data satisfies Zod schema `OrientStoryDataSchema`
- [x] ErrorConsistency:
  - Mock loader to throw `ConfirmStoryError("DATA_NOT_FOUND")`
  - Assert error UI with retry button rendered

### Implementation ✅

- [x] Zod schema: `OrientStoryDataSchema` → `server/data_structures/ConfirmStory.ts`
- [x] Data loader: calls `GET /api/story/orient-context` → `data_loaders/loadOrientStoryData.ts`
- [x] API route fetches from Supabase → `app/api/story/orient-context/route.ts`
- [x] Error definitions → `server/error_definitions/ConfirmStoryErrors.ts`
- [x] DAO → `server/data_access_objects/ConfirmStoryDAO.ts`

---

## Step 2: Submit selected story confirmation ✅

**From path spec:**
- [x] Input: Selected story ID from ui-w8p2, validated by ui-a4y1, sent via api-q7v1 to api-m5g7
- [x] Process: Capture ID on confirm and POST to backend
- [x] Output: Backend receives confirmation request with questionId + storyId
- [x] Error:
  - No story selected → frontend blocks
  - Transit failure → backend_error_definitions error → UI failure message

### Test (Frontend + API contract) ✅
`frontend/components/__tests__/story-selection-submit.test.tsx` — **11 tests passing**

- [x] Reachability:
  - Select story → click confirm
  - Assert `confirmStory()` called with { questionId, storyId }
- [x] TypeInvariant:
  - Assert payload matches `ConfirmStoryRequestSchema`
- [x] ErrorConsistency:
  - No selection → confirm disabled + validation message
  - Mock 500 → UI shows submission failure message

### Implementation ✅

- [x] `StorySelectionVerifier.ts`: ensure exactly one story selected → `verifiers/StorySelectionVerifier.ts`
- [x] `confirmStory.ts`: typed fetch wrapper → `api_contracts/confirmStory.ts`
- [x] `StorySelection.tsx`: component → `components/StorySelection.tsx`
- [x] Disable confirm button when invalid

---

## Step 3: Validate story alignment and eligibility ✅

**From path spec:**
- [x] Input: { questionId, storyId } + records from db-f8n5
- [x] Process: db-j6x9 validates existence, association, alignment, not already confirmed
- [x] Output: Validation success result
- [x] Error: Domain error mapped to db-l1c3

### Test (Backend) ✅
`server/verifiers/__tests__/story-alignment-verifier.test.ts` — **8 tests passing**

- [x] Reachability:
  - Given valid story + question + requirements
  - Expect `validate()` returns success
- [x] TypeInvariant:
  - Assert return type is `ValidationResult` union
- [x] ErrorConsistency:
  - Story not found → `STORY_NOT_FOUND`
  - Already confirmed → `STORY_ALREADY_CONFIRMED`
  - Not aligned → `STORY_NOT_ALIGNED`

### Implementation ✅

- [x] `StoryAlignmentVerifier.validate(question, story, requirements, availableStories)` → `server/verifiers/StoryAlignmentVerifier.ts`
- [x] Returns typed `ValidationResult`
- [x] Errors defined in `server/error_definitions/ConfirmStoryErrors.ts`

---

## Step 4: Mark story as confirmed and restrict scope ✅

**From path spec:**
- [x] Input: Validated request + story record
- [x] Process: db-h2s4 coordinates DAO to:
  - Mark selected story confirmed
  - Mark others excluded
- [x] Output: Persisted state with exactly one confirmed story
- [x] Error: DAO persistence failure → abort without partial updates

### Test (Service + DAO) ✅
`server/services/__tests__/confirm-story-service.test.ts` — **9 tests passing**

- [x] Reachability:
  - Seed 3 stories for question
  - Confirm 1
  - Assert exactly one `status=CONFIRMED`, others `status=EXCLUDED`
- [x] TypeInvariant:
  - Assert service returns `ConfirmStoryResponseSchema`
- [x] ErrorConsistency:
  - Simulate DAO failure mid-transaction
  - Assert no story status changed (transaction rollback)

### Implementation ✅

- [x] `ConfirmStoryDAO.updateStatusesTransactional(questionId, storyId)` → `server/data_access_objects/ConfirmStoryDAO.ts`
- [x] `ConfirmStoryService.confirm()` orchestrates verifier + DAO → `server/services/ConfirmStoryService.ts`
- [x] API route → `app/api/story/confirm/route.ts`

---

## Step 5: Display confirmed story for next step ✅

**From path spec:**
- [x] Input: Successful confirmation response
- [x] Process: Update UI state and navigate to next step
- [x] Output: Only confirmed story shown
- [x] Error: Response processing failure → show error, remain on screen

### Test (Frontend Integration) ✅
`modules/orient-story/__tests__/confirm-success-navigation.test.tsx` — **7 tests passing**

- [x] Reachability:
  - Mock successful API response
  - Assert only confirmed story rendered
- [x] TypeInvariant:
  - Assert response matches `ConfirmStoryResponseSchema`
- [x] ErrorConsistency:
  - Mock server failure
  - Assert error message shown and no navigation

### Implementation ✅

- [x] Update module state with confirmed story → `OrientStoryModule.tsx` state machine
- [x] Guard against invalid response via Zod parse → `confirmStory.ts`

---

## Terminal Condition ✅

### Integration Test ✅
`server/__tests__/confirmAlignedStorySelection.integration.test.ts` — **11 tests passing**

- [x] Seed question + job requirements + 3 aligned stories
- [x] Simulate:
  1. Load context
  2. Submit confirmation
  3. Validate + persist
  4. Fetch next step state
- [x] Assert:
  - Exactly one story `CONFIRMED`
  - Others excluded
  - API returns only confirmed story
  - Types preserved across boundaries

This proves full Reachability from trigger to terminal condition.

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/313-confirm-aligned-story-selection.md`
- Gate 1 Requirement: `F-ORIENT-STORY`
- Verification output (TLC): `ConfirmAlignedStorySelection.tla`
