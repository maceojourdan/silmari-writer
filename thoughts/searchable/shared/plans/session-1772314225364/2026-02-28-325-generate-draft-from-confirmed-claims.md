# generate-draft-from-confirmed-claims TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/325-generate-draft-from-confirmed-claims.md`

Tech Stack (Gate 2 – Option 1):
- Frontend: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- Backend: Next.js API Routes (Node.js), TypeScript, Zod
- Database: Supabase (PostgreSQL)

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/325-generate-draft-from-confirmed-claims.md
```

Stdout:
```
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
```

Exit code: `0`

This TDD plan mirrors those properties at code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|---------------|------------------------|
| ui-w8p2 | component | `frontend/components/GenerateDraftButton.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/draftRequestVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/generateDraft.ts` |
| api-m5g7 | endpoint | `backend/endpoints/generateDraft.ts` (Next.js route handler) |
| api-n8k2 | request_handler | `backend/request_handlers/generateDraftHandler.ts` |
| db-h2s4 | service | `backend/services/DraftGenerationService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/StoryDao.ts` |
| db-f8n5 | data_structure | `backend/data_structures/StoryStructures.ts` (Claim, Draft schemas) |
| cfg-d2q3 | common_structure | `shared/common_structures/DraftDocumentStructure.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/DraftErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |

---

## Step 1: Initiate draft generation request

**From path spec:**
- Input: User action from `ui-w8p2` invoking `api-q7v1`
- Process: Capture claim set context and send request
- Output: HTTP request to `api-m5g7`
- Error: Client validation fails via `ui-a4y1`

### Test (`frontend/components/__tests__/GenerateDraftButton.test.tsx`)

- [x] Reachability:
  - [x] Render component with valid `claimSetId`
  - [x] Click “Generate Draft”
  - [x] Assert `generateDraft()` API contract called with `{ claimSetId }`
- [x] TypeInvariant:
  - [x] Assert request payload matches Zod schema in `generateDraft.ts`
- [x] ErrorConsistency:
  - [x] Provide invalid context (missing `claimSetId`)
  - [x] Assert verifier blocks submission and validation message renders
  - [x] Assert API contract NOT called

### Implementation

- [x] `draftRequestVerifier.ts`: Zod schema `{ claimSetId: string().uuid() }`
- [x] `generateDraft.ts`: typed function wrapping `fetch('/api/generate-draft')`
- [x] `GenerateDraftButton.tsx`:
  - [x] On click → validate → call contract → render errors if invalid

---

## Step 2: Handle draft generation endpoint request

**From path spec:**
- Input: HTTP request to `api-m5g7`
- Process: Validate params, delegate to service
- Output: Invocation of `db-h2s4`
- Error:
  - Auth failure → `cfg-j9w2`
  - Invalid params → `db-l1c3`

### Test (`backend/endpoints/__tests__/generateDraft.test.ts`)

- [x] Reachability:
  - [x] Mock authenticated request with valid body
  - [x] Assert handler calls `DraftGenerationService.generate(claimSetId)`
- [x] TypeInvariant:
  - [x] Assert parsed body matches backend Zod schema
  - [x] Assert response JSON matches Draft DTO type
- [x] ErrorConsistency:
  - [x] Invalid body → 400 with `DraftErrors.INVALID_PARAMETERS`
  - [x] Claim set not found → 404
  - [x] No confirmed claims → 422
  - [x] Unexpected error → 500

### Implementation

- [x] `generateDraft.ts` route handler:
  - [x] Zod body validation
  - [x] Delegate to `generateDraftHandler.ts`
- [x] `generateDraftHandler.ts`:
  - [x] Calls `DraftGenerationService.generate()`
  - [x] Maps thrown errors to HTTP responses

---

## Step 3: Retrieve confirmed claims

**From path spec:**
- Input: claimSetId
- Process: DAO query → filter status = 'confirmed'
- Output: Collection of confirmed claim entities
- Error: claim set not found OR no confirmed claims

### Test (`backend/services/__tests__/DraftGenerationService.retrieveClaims.test.ts`)

- [x] Reachability:
  - [x] Seed DB with claims (confirmed + unconfirmed)
  - [x] Call `generate()`
  - [x] Assert only confirmed claims passed to transform step
- [x] TypeInvariant:
  - [x] Assert returned array conforms to `Claim` type (from `StoryStructures.ts`)
- [x] ErrorConsistency:
  - [x] No claim set → throw `DraftErrors.CLAIM_SET_NOT_FOUND`
  - [x] No confirmed claims → throw `DraftErrors.NO_CONFIRMED_CLAIMS`

### Implementation

- [x] `StoryDAO.ts`:
  - [x] `getClaimsBySetId(claimSetId)`
- [x] `DraftGenerationService.generate()`:
  - [x] Fetch claims
  - [x] Filter `status === 'CONFIRMED'`
  - [x] Throw errors from `DraftErrors.ts` as required

---

## Step 4: Transform confirmed claims into structured draft

**From path spec:**
- Input: confirmed claims + `DraftDocumentStructure`
- Process: Organize into defined sections/order
- Output: Structured draft object
- Error: Structural inconsistency → `cfg-j9w2`

### Test (`backend/services/__tests__/DraftGenerationService.transform.test.ts`)

- [x] Reachability:
  - [x] Provide confirmed claims with valid structural metadata
  - [x] Assert output draft sections match `DraftDocumentStructure`
- [x] TypeInvariant:
  - [x] Assert output matches `Draft` schema from `StoryStructures.ts`
- [x] ErrorConsistency:
  - [x] Missing required structural field → throw `SharedErrors.TRANSFORMATION_ERROR`

### Implementation

- [x] `DraftDocumentStructure.ts`:
  - [x] Defines ordered sections (Context, Actions, Outcome)
- [x] `DraftGenerationService.transformClaimsToDraft()`:
  - [x] Group claims by section
  - [x] Validate required sections
  - [x] Construct Draft DTO

---

## Step 5: Persist and return generated draft

**From path spec:**
- Input: Structured draft
- Process: Persist via DAO, return via endpoint
- Output: HTTP response containing structured draft; UI renders
- Error: Persistence failure → `db-l1c3`

### Test (Backend) (`backend/services/__tests__/DraftGenerationService.persist.test.ts`)

- [x] Reachability:
  - [x] Mock DAO `saveDraft()` success
  - [x] Assert draft persisted and returned
- [x] TypeInvariant:
  - [x] Assert saved draft matches Draft schema
- [x] ErrorConsistency:
  - [x] Simulate DB error → throw `DraftErrors.PERSISTENCE_FAILED`

### Test (Frontend Integration) (`frontend/components/__tests__/GenerateDraft.integration.test.tsx`)

- [x] Mock successful API response
- [x] Click button
- [x] Await draft render
- [x] Assert UI shows only confirmed claims

### Implementation

- [x] `StoryDAO.saveDraft(draft)`
- [x] Service wraps persistence in try/catch and throws `DraftErrors.PERSISTENCE_FAILED`
- [x] Endpoint serializes Draft DTO
- [x] `GenerateDraftButton.tsx` renders draft preview view on success

---

## Terminal Condition

### Integration Test (`e2e/generate-draft.spec.ts` – Playwright)

- Seed DB with:
  - Confirmed and unconfirmed claims
- Log in as authenticated user
- Click “Generate Draft”
- Assert:
  - HTTP 200
  - UI displays structured draft
  - Draft contains ONLY confirmed claims
  - Sections match `DraftDocumentStructure`

This proves:
- Reachability: Full trigger → terminal path exercised
- TypeInvariant: Types enforced at every boundary
- ErrorConsistency: Each failure path returns defined error state

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/325-generate-draft-from-confirmed-claims.md`
- Gate 1 Requirement: `F-DRAFT-GENERATE`
- TLA+ Artifact: `frontend/artifacts/tlaplus/325-generate-draft-from-confirmed-claims/GenerateDraftFromConfirmedClaims.tla`

---

## Validation Report

**Validated at**: 2026-03-01T16:25:00Z

### Implementation Status
✓ Step 1: Initiate draft generation request — Fully implemented
✓ Step 2: Handle draft generation endpoint request — Fully implemented
✓ Step 3: Retrieve confirmed claims — Fully implemented
✓ Step 4: Transform confirmed claims into structured draft — Fully implemented
✓ Step 5: Persist and return generated draft — Fully implemented
✗ Terminal Condition: E2E Playwright test — **Missing** (`e2e/generate-draft.spec.ts` does not exist)
⚠️ Git status: All implementation files are **untracked** (never committed)

### Automated Verification Results
✓ Path 325 tests pass: 50/50 tests across 7 test files (`vitest run`)
✓ Full test suite: 2874 passed, 9 skipped (8 failures pre-existing in `ButtonInteractions.test.tsx` — voice chat, unrelated)
⚠️ TypeScript type-check: Pre-existing errors in `behavioralQuestionVerifier.test.ts` (unrelated to path 325)
⚠️ ESLint: Not run on path 325 files in isolation (no blocking issues surfaced via tests/TS)

### File Inventory (22/23 present)

| Plan Resource | Actual Path | Status |
|---|---|---|
| `draftRequestVerifier.ts` | `frontend/src/verifiers/draftRequestVerifier.ts` | ✓ |
| `generateDraft.ts` (contract) | `frontend/src/api_contracts/generateDraft.ts` | ✓ |
| `GenerateDraftButton.tsx` | `frontend/src/components/GenerateDraftButton.tsx` | ✓ |
| `generateDraft.ts` (endpoint) | `frontend/src/app/api/generate-draft/route.ts` | ✓ |
| `generateDraftHandler.ts` | `frontend/src/server/request_handlers/generateDraftHandler.ts` | ✓ |
| `DraftGenerationService.ts` | `frontend/src/server/services/DraftGenerationService.ts` | ✓ |
| `StoryDAO.ts` | `frontend/src/server/data_access_objects/StoryDAO.ts` | ✓ |
| `StoryStructures.ts` | `frontend/src/server/data_structures/StoryStructures.ts` | ✓ |
| `DraftDocumentStructure.ts` | `frontend/src/server/data_structures/DraftDocumentStructure.ts` | ✓ |
| `DraftErrors.ts` | `frontend/src/server/error_definitions/DraftErrors.ts` | ✓ |
| `SharedErrors.ts` | `frontend/src/server/error_definitions/SharedErrors.ts` | ✓ |
| `GenerateDraftButton.test.tsx` | `frontend/src/components/__tests__/GenerateDraftButton.test.tsx` | ✓ |
| `GenerateDraft.integration.test.tsx` | `frontend/src/components/__tests__/GenerateDraft.integration.test.tsx` | ✓ |
| `generateDraft.test.ts` (endpoint) | `frontend/src/app/api/generate-draft/__tests__/route.test.ts` | ✓ |
| `generateDraftHandler.test.ts` | `frontend/src/server/request_handlers/__tests__/generateDraftHandler.test.ts` | ✓ |
| `DraftGenerationService.retrieveClaims.test.ts` | `frontend/src/server/services/__tests__/DraftGenerationService.step3.test.ts` | ✓ |
| `DraftGenerationService.transform.test.ts` | `frontend/src/server/services/__tests__/DraftGenerationService.step4.test.ts` | ✓ |
| `DraftGenerationService.persist.test.ts` | `frontend/src/server/services/__tests__/DraftGenerationService.step5.test.ts` | ✓ |
| `GenerateDraftFromConfirmedClaims.tla` | `artifacts/tlaplus/325-generate-draft-from-confirmed-claims/GenerateDraftFromConfirmedClaims.tla` | ✓ |
| `GenerateDraftFromConfirmedClaims.cfg` | `artifacts/tlaplus/325-generate-draft-from-confirmed-claims/GenerateDraftFromConfirmedClaims.cfg` | ✓ |
| Path spec | `specs/orchestration/session-1772314225364/325-generate-draft-from-confirmed-claims.md` | ✓ |
| TDD plan | `thoughts/.../2026-02-28-325-generate-draft-from-confirmed-claims.md` | ✓ |
| **`e2e/generate-draft.spec.ts`** | **Does not exist** | ✗ |

### Code Review Findings

#### Matches Plan:
- **Step 1**: `draftRequestVerifier.ts` has exact Zod schema `{ claimSetId: z.string().uuid() }`. `generateDraft.ts` wraps `fetch('/api/generate-draft')` with pre-send and post-receive Zod validation. `GenerateDraftButton.tsx` follows validate → call → render errors flow precisely.
- **Step 2**: `route.ts` has Zod body validation with correct error mapping (400/404/422/500). `generateDraftHandler.ts` calls `DraftGenerationService.generate()` and maps errors correctly. Error codes (`INVALID_PARAMETERS`, `CLAIM_SET_NOT_FOUND`, `NO_CONFIRMED_CLAIMS`) are carried via `statusCode` on the error objects.
- **Step 3**: `StoryDAO.getClaimsBySetId(claimSetId)` exists. Service filters `status === 'CONFIRMED'`. Throws `CLAIM_SET_NOT_FOUND` (null return) and `NO_CONFIRMED_CLAIMS` (empty filtered array) correctly.
- **Step 4**: `DraftDocumentStructure` defines ordered sections `['context', 'actions', 'outcome']`. Service groups claims by section, validates required sections, constructs `StructuredDraft` DTO. Missing sections throw `SharedErrors.TransformationError` (422).
- **Step 5**: `StoryDAO.saveDraft(draft)` exists. Service wraps in try/catch, throws `DraftDataAccessError.PERSISTENCE_FAILED` (500, retryable). `generate()` orchestrates retrieve → transform → persist correctly.

#### Deviations from Plan:
- **E2E test absent**: The plan specifies `e2e/generate-draft.spec.ts` (Playwright) as the Terminal Condition. This file was never created. The frontend integration test (`GenerateDraft.integration.test.tsx`) partially covers the end-to-end user flow using mocked API responses, but does not exercise the actual backend.
- **Files not committed**: All 22 implementation files exist on disk as untracked files. No commit for path 325 exists on any branch. The plan's checkboxes are all marked `[x]` but the work was never preserved in version control.
- **DAO stubs**: `StoryDAO.getClaimsBySetId` and `StoryDAO.saveDraft` throw `new Error('not yet wired to Supabase')`. This is consistent with the TDD pattern used across the codebase but means the data access layer is not connected to the real database.

#### Issues Found:
- **CRITICAL — E2E test missing**: Terminal Condition (Playwright E2E proving full Reachability/TypeInvariant/ErrorConsistency across the entire stack) is not implemented.
- **CRITICAL — Nothing committed**: All work exists only in the working directory. A `git clean` or filesystem event would destroy the implementation.
- **MODERATE — SharedError branch untested in route**: `route.ts` catches `SharedError` instances (lines 59-64), but no test exercises this path (e.g., `TRANSFORMATION_ERROR` propagating up from the service through the handler to the route).
- **MODERATE — Invalid section name branch untested**: `DraftGenerationService.transformClaimsToDraft` throws `TransformationError` when `!DraftDocumentStructure.isValidSection(claim.section)` (line 79), but no step4 test provides a claim with an invalid section string.
- **MINOR — `@ts-nocheck` in UI test files**: Both `GenerateDraftButton.test.tsx` and `GenerateDraft.integration.test.tsx` use `@ts-nocheck`, suppressing TypeScript enforcement and weakening the TypeInvariant property at the test level.
- **MINOR — Structural type assertions**: UI tests assert payload structure via `toHaveProperty` rather than Zod `safeParse`, providing weaker TypeInvariant guarantees than the backend tests.

### Manual Testing Required:
- [ ] Wire `StoryDAO` to Supabase and verify end-to-end with real data
- [ ] Create `e2e/generate-draft.spec.ts` Playwright test per Terminal Condition spec
- [ ] Verify claim filtering with mixed confirmed/unconfirmed claims against real DB
- [ ] Test with edge cases: very large claim sets, concurrent draft generation
- [ ] Verify section ordering is preserved in rendered UI

### Recommendations:
1. **Commit the implementation immediately** — all work is at risk of being lost
2. **Create the E2E Playwright test** — this is the Terminal Condition and must be present to consider the path complete per the TDD plan
3. **Add test for SharedError branch** in `route.test.ts` — simulate a `TRANSFORMATION_ERROR` from the handler
4. **Add test for invalid section name** in `step4.test.ts` — provide a claim with an unrecognized section value
5. **Remove `@ts-nocheck`** from UI test files and fix any resulting type errors
6. **Wire DAO stubs to Supabase** when the database layer is ready (consistent with other paths)

VALIDATION_RESULT: FAIL
