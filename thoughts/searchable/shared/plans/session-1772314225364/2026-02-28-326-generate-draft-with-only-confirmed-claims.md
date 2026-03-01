# generate-draft-with-only-confirmed-claims TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/326-generate-draft-with-only-confirmed-claims.md`

Tech Stack: **Option 1 – Next.js (TypeScript) + API Routes + Supabase (Postgres)**  
Test Runner: **Vitest (unit) + React Testing Library (frontend) + Supertest (API route tests)**

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- **Reachability**
- **TypeInvariant**
- **ErrorConsistency**

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/326-generate-draft-with-only-confirmed-claims.md
```

Verification result:
```
Result: ALL PROPERTIES PASSED
States: 26 found, 13 distinct, depth 0
Properties: Reachability, TypeInvariant, ErrorConsistency
```

This TDD plan mirrors those properties at code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/DraftGenerator.tsx` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/generateDraft.ts` |
| api-m5g7 | endpoint | `frontend/app/api/draft/generate/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/GenerateDraftHandler.ts` |
| db-h2s4 | service | `backend/services/DraftGenerationService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/ClaimDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Claim.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/DraftErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

---

## Step 1: Initiate draft generation request

**From path spec:**
- Input: User action from `ui-w8p2` invoking `api-q7v1`.
- Process: Capture case context and send request to backend endpoint.
- Output: HTTP request to `api-m5g7`.
- Error: If request cannot be formed/sent, log via `cfg-r3d7` and show error.

### Test (`frontend/components/__tests__/DraftGenerator.test.tsx`)

- [x] **Reachability**:
  Render component with valid `caseId`. Click “Generate Draft”. Assert `generateDraft(caseId)` called.
- [x] **TypeInvariant**:
  Assert `generateDraft` is called with `{ caseId: string }`.
- [x] **ErrorConsistency**:
  Mock contract to reject. Assert:
  - `frontend/logging.error` called
  - Error message rendered
  - No draft rendered

### Implementation

- [x] `DraftGenerator.tsx`
  - Button triggers `generateDraft({ caseId })`
  - `try/catch` logs via `frontend/logging`
  - Local state: `draft | error`
- [x] `frontend/api_contracts/generateDraft.ts`
  - Typed function using `fetch('/api/draft/generate', { method: 'POST' })`
  - Zod schema for request body `{ caseId: string }`

---

## Step 2: Handle draft generation endpoint

**From path spec:**  
- Input: HTTP request to `api-m5g7`.  
- Process: Validate structure and delegate to handler.  
- Output: Invocation of `api-n8k2`.  
- Error: Validation failure → structured backend error (`db-l1c3`).

### Test (`frontend/app/api/draft/generate/__tests__/route.test.ts`)

- [x] **Reachability**:
  POST valid `{ caseId }`. Assert handler invoked.
- [x] **TypeInvariant**:
  Invalid body (missing caseId) → 400 with `DraftErrors.ValidationError` shape.
- [x] **ErrorConsistency**:
  Assert JSON response matches error schema `{ code, message }`.

### Implementation

- [x] `route.ts`
  - Parse JSON
  - Zod validation
  - On success → call `GenerateDraftHandler.execute`
  - On failure → return `DraftErrors.ValidationError`

---

## Step 3: Orchestrate draft generation

**From path spec:**  
- Input: Command from handler.  
- Process: Invoke service.  
- Output: Call to `db-h2s4`.  
- Error: Service failure logged (`cfg-q9c5`) and propagated.

### Test (`backend/request_handlers/__tests__/GenerateDraftHandler.test.ts`)

- [x] **Reachability**:
  Mock service → assert `DraftGenerationService.generate(caseId)` called.
- [x] **TypeInvariant**:
  Assert return type is `StructuredDraft`.
- [x] **ErrorConsistency**:
  Mock service throw → assert:
  - `backend/logging.error` called
  - Error rethrown as `DraftErrors.GenerationError`

### Implementation

- [x] `GenerateDraftHandler.ts`
  - `execute({ caseId })`
  - `try/catch` logs via backend logger
  - Delegates to service

---

## Step 4: Retrieve and filter confirmed claims

**From path spec:**  
- Input: Case context.  
- Process: Retrieve all claims, filter `status === 'confirmed'`.  
- Output: Collection of confirmed claims.  
- Error: Retrieval failure → data access error; empty confirmed set allowed.

### Test (`backend/services/__tests__/DraftGenerationService.filter.test.ts`)

- [x] **Reachability**:
  DAO returns mix: confirmed/unconfirmed/rejected.
  Assert only confirmed returned.
- [x] **TypeInvariant**:
  Assert each item matches `Claim` type from `Claim.ts`.
- [x] **ErrorConsistency**:
  DAO throws → expect `DraftErrors.DataAccessError`.
- [x] **Edge (No confirmed claims)**:
  DAO returns only unconfirmed/rejected → expect empty array.

### Implementation

- [x] `Claim.ts`
  ```ts
  export type ClaimStatus = 'confirmed' | 'unconfirmed' | 'rejected';
  export interface Claim {
    id: string;
    caseId: string;
    text: string;
    status: ClaimStatus;
    metadata?: Record<string, unknown>;
  }
  ```
- [x] `ClaimDAO.ts`
  - `getClaimsByCaseId(caseId)` using Supabase client
- [x] `DraftGenerationService.ts`
  - `const claims = await dao.getClaimsByCaseId(caseId)`
  - `return claims.filter(c => c.status === 'confirmed')`

---

## Step 5: Generate structured draft from confirmed claims

**From path spec:**  
- Input: Filtered confirmed claims.  
- Process: Compose structured draft excluding others.  
- Output: Structured draft entity.  
- Error: Invalid claim structure → backend error.

### Test (`backend/services/__tests__/DraftGenerationService.compose.test.ts`)

- [x] **Reachability**:
  Input confirmed claims → output draft contains all claim texts.
- [x] **TypeInvariant**:
  Assert draft matches:
  ```ts
  interface StructuredDraft {
    caseId: string;
    content: string;
    claimsUsed: string[];
  }
  ```
- [x] **ErrorConsistency**:
  Claim missing required `text` → expect `DraftErrors.GenerationError`.

### Implementation

- [x] In `DraftGenerationService.generate(caseId)`:
  - Retrieve confirmed claims
  - Validate structure
  - Compose:
    ```ts
    return {
      caseId,
      content: confirmed.map(c => c.text).join('\n\n'),
      claimsUsed: confirmed.map(c => c.id)
    }
    ```

---

## Step 6: Return and display structured draft

**From path spec:**  
- Input: Structured draft via API contract.  
- Process: Update UI state and render draft.  
- Output: Rendered draft with only confirmed claims.  
- Error: Rendering failure → log + show message.

### Test (`frontend/components/__tests__/DraftGenerator.render.test.tsx`)

- [x] **Reachability**:
  Mock API returns draft. Assert draft content rendered.
- [x] **TypeInvariant**:
  Assert rendered claims match `claimsUsed`.
- [x] **ErrorConsistency**:
  Force render error → assert `frontend/logging.error` called and fallback message shown.

### Implementation

- [x] `DraftGenerator.tsx`
  - `setDraft(response)`
  - Render `draft.content`
  - Guard against undefined
  - Error boundary or conditional rendering with logger

---

## Terminal Condition

### Integration Test (`frontend/components/__tests__/DraftGenerator.integration.test.tsx`)

**Scenario:** Case contains:
- [x] 2 confirmed claims
- [x] 1 unconfirmed claim
- [x] 1 rejected claim

**Execution:**
- [x] Trigger UI button
- [x] API → Handler → Service → DAO (mocked DB)

**Assertions:**
- [x] Draft content includes both confirmed claims
- [x] Draft excludes unconfirmed/rejected claims
- [x] `claimsUsed` contains only confirmed IDs
- [x] UI displays structured draft

This proves:
- [x] **Reachability:** End-to-end path executes
- [x] **TypeInvariant:** Types preserved across boundaries
- [x] **ErrorConsistency:** All error branches return structured errors

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/326-generate-draft-with-only-confirmed-claims.md`
- Gate 1 Requirement: `F-DRAFT-GENERATE`
- TLA+ Artifact: `frontend/artifacts/tlaplus/326-generate-draft-with-only-confirmed-claims/GenerateDraftWithOnlyConfirmedClaims.tla`
