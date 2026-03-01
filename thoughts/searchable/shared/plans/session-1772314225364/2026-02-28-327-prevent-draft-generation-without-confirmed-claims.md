# prevent-draft-generation-without-confirmed-claims TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/327-prevent-draft-generation-without-confirmed-claims.md

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/327-prevent-draft-generation-without-confirmed-claims.md
```

Verification output:

- Result: ALL PROPERTIES PASSED  
- States: 22 found, 11 distinct  
- Exit code: 0  
- Properties: Reachability, TypeInvariant, ErrorConsistency

This TDD plan mirrors those three properties at code level.

---

## Tech Stack (Gate 2 – Option 1)

- Frontend: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- Backend: Next.js API Routes (Node.js, TypeScript, Zod)
- Database: Supabase (Postgres)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/DraftGeneratorButton.tsx` |
| ui-v3n6 | module | `frontend/modules/draft/DraftModule.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/draftPreconditionsVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/generateDraft.ts` |
| api-m5g7 | endpoint | `frontend/app/api/draft/generate/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/GenerateDraftRequestHandler.ts` |
| db-h2s4 | service | `backend/services/DraftGenerationService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/ClaimsDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Claim.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/DraftErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |

---

## Step 1: Initiate draft generation request

**From path spec:**
- Input: User interaction in ui-w8p2 within ui-v3n6
- Process: Capture click → trigger draft generation via api-q7v1
- Output: Draft generation API request sent
- Error: If invalid UI state, ui-a4y1 blocks and displays validation message

### Test (`frontend/components/__tests__/DraftGeneratorButton.test.tsx`)

- [x] Reachability: Render `DraftModule` → click "Generate Draft" → assert `generateDraft()` called.
- [x] TypeInvariant: Assert API contract is invoked with typed `GenerateDraftRequest`.
- [x] ErrorConsistency: Mock verifier to return invalid → assert no API call and validation message rendered.

### Implementation

- [x] Implement `draftPreconditionsVerifier.ts` returning `{ valid: boolean; message?: string }`.
- [x] `DraftGeneratorButton`:
  - On click → run verifier.
  - If valid → call `generateDraft(request)`.
  - If invalid → set local error state and render message.

---

## Step 2: Receive and route draft generation request

**From path spec:**
- Input: HTTP POST `/api/draft/generate`
- Process: Endpoint delegates to `GenerateDraftRequestHandler`
- Output: Invocation of `DraftGenerationService`
- Error: Malformed/unauthorized → error from `DraftErrors`

### Test (`frontend/app/api/draft/generate/__tests__/route.test.ts`)

- [x] Reachability: POST valid body → assert handler invoked.
- [x] TypeInvariant: Invalid schema → 400 with typed error response.
- [x] ErrorConsistency: Unauthorized request → 401 with `UNAUTHORIZED` error code.

### Implementation

- [x] Zod schema for `GenerateDraftRequest`.
- [x] API route parses body, validates via Zod.
- [x] On success → call `GenerateDraftRequestHandler.handle()`.
- [x] Map thrown `DraftErrors` to HTTP responses.

---

## Step 3: Check for confirmed claims

**From path spec:**
- Input: DraftGenerationService receives request
- Process: ClaimsDAO retrieves claims → evaluate confirmed status
- Output: Determination that zero confirmed claims exist
- Error:
  - Data retrieval failure → DATA_ACCESS_ERROR
  - Zero confirmed claims → NO_CONFIRMED_CLAIMS

### Test (`backend/services/__tests__/DraftGenerationService.test.ts`)

- [x] Reachability: Mock DAO returning claims with all `confirmed=false` → expect `NoConfirmedClaimsError`.
- [x] TypeInvariant: DAO returns `Claim[]` (with `confirmed: boolean`) → service processes typed array.
- [x] ErrorConsistency:
  - [x] DAO throws → expect `DataAccessError`.
  - [x] No confirmed claims → expect `NoConfirmedClaimsError`.

### Implementation

- [x] `Claim` type in `Claim.ts`:
  ```ts
  export interface Claim {
    id: string;
    storyRecordId: string;
    confirmed: boolean;
    content: string;
  }
  ```
- [x] `ClaimsDAO.getClaimsByStoryRecordId()`.
- [x] `DraftGenerationService.generateDraft()`:
  - Fetch claims.
  - If none confirmed → throw `NoConfirmedClaimsError`.

---

## Step 4: Return no-confirmed-claims response

**From path spec:**
- Input: NoConfirmedClaimsError
- Process: Map domain error → HTTP error with user-facing message
- Output: HTTP response with no draft payload
- Error: Mapping failure → GENERIC_ERROR fallback

### Test (`backend/request_handlers/__tests__/GenerateDraftRequestHandler.test.ts`)

- [x] Reachability: Mock service throwing `NoConfirmedClaimsError` → expect HTTP 400 with code `NO_CONFIRMED_CLAIMS`.
- [x] TypeInvariant: Response body matches `ErrorResponse` type.
- [x] ErrorConsistency: Unknown error → HTTP 500 with `GENERIC_ERROR` and safe message.

### Implementation

- [x] `DraftErrors.ts` defines:
  - `NoConfirmedClaimsError`
  - `DataAccessError`
  - `GenericDraftError`
- [x] Handler catches domain errors and maps to HTTP status + shared error code from `SharedErrors.ts`.

---

## Step 5: Display no confirmed claims message

**From path spec:**
- Input: Error response in frontend
- Process: Component interprets error → updates state
- Output: Visible message; no draft rendered
- Error: Parsing failure → generic error notification

### Test (`frontend/modules/draft/__tests__/DraftModule.test.tsx`)

- [x] Reachability: Mock API returning `NO_CONFIRMED_CLAIMS` → assert message rendered and no draft content.
- [x] TypeInvariant: Error response matches shared `ErrorResponse` type.
- [x] ErrorConsistency: Malformed error → fallback generic notification displayed.

### Implementation

- [x] `generateDraft()` in API contract parses JSON into typed `ErrorResponse`.
- [x] `DraftModule`:
  - If error.code === `NO_CONFIRMED_CLAIMS` → set `uiError`.
  - Render `<ErrorNotification />` using shared definitions from `SharedErrors.ts`.
  - Ensure no draft state is set.

---

## Terminal Condition

### Integration Test (`tests/integration/preventDraftWithoutConfirmedClaims.test.ts`)

- [x] Seed DB with claims where all `confirmed=false`.
- [x] Render UI → click "Generate Draft".
- [x] Assert:
  - [x] API returns 400 with `NO_CONFIRMED_CLAIMS`.
  - [x] UI displays "No confirmed claims are available.".
  - [x] No draft content exists in DOM.

This proves:
- [x] Reachability: Trigger → UI → API → Service → Error → UI.
- [x] TypeInvariant: Typed request/response across layers.
- [x] ErrorConsistency: All error branches produce valid error states.

---

## References

- Path: 327-prevent-draft-generation-without-confirmed-claims.md
- Requirement: F-DRAFT-GENERATE (Acceptance Criterion #4)
- Shared errors: cfg-j9w2
- Backend errors: db-l1c3
