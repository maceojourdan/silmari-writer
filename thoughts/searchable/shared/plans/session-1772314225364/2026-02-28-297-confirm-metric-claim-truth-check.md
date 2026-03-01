# confirm-metric-claim-truth-check TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/297-confirm-metric-claim-truth-check.md`

Tech Stack (Gate 2 – Option 1):
- Frontend: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- Backend: Next.js API Routes (Node.js), TypeScript, Zod
- Database: Supabase (Postgres)

---

## Verification (Phase 0)

Command executed:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/297-confirm-metric-claim-truth-check.md
```

Result (from verification_results_json):
- Status: `verified`
- Exit code: `0`
- Output: `Result: ALL PROPERTIES PASSED`
- States: `22 found, 11 distinct`
- Properties proven:
  - Reachability
  - TypeInvariant
  - ErrorConsistency

This TDD plan maps each of those properties to concrete test assertions at code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/ConfirmMetricClaim.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/confirmMetricClaimVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/confirmTruthCheck.ts` |
| api-m5g7 | endpoint | `app/api/truth-checks/confirm/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/ConfirmTruthCheckHandler.ts` |
| db-h2s4 | service | `backend/services/TruthCheckService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/TruthCheckDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/TruthCheck.ts` (maps to `truth_checks` table) |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/TruthCheckErrors.ts` |

---

## Step 1: Submit confirmation decision - [x] Complete

**From path spec:**
- Input: User decision (Y/N), metric claim identifier, and source displayed in frontend component (ui-w8p2).
- Process: Capture selection and prepare structured confirmation payload (claim_id, status, source).
- Output: Structured confirmation request ready for frontend API contract (api-q7v1).
- Error: If no selection is made, block submission via frontend_verifier (ui-a4y1) and display inline validation error.

### Test
`frontend/components/__tests__/ConfirmMetricClaim.test.tsx`

- Reachability:
  - Render component with `claimId` + `source`.
  - Select “Y”.
  - Click submit.
  - Assert payload `{ claim_id, status: "confirmed", source }` passed to API contract mock.

- TypeInvariant:
  - Assert `status` is union type: `"confirmed" | "denied"`.
  - Assert `claim_id` is string and `source` is string.

- ErrorConsistency:
  - Do not select Y/N.
  - Click submit.
  - Assert verifier prevents API call.
  - Assert inline validation error is rendered.

### Implementation

- `confirmMetricClaimVerifier.ts`
  - Function `validateDecision(decision?: "Y" | "N")` → throws or returns error if undefined.

- `ConfirmMetricClaim.tsx`
  - Local state: `decision: "Y" | "N" | null`.
  - Map Y → `confirmed`, N → `denied`.
  - On submit:
    - Run verifier.
    - Build payload:
      ```ts
      type ConfirmTruthCheckRequest = {
        claim_id: string;
        status: "confirmed" | "denied";
        source: string;
      }
      ```
    - Call API contract.

---

## Step 2: Send confirmation request - [x] Complete

**From path spec:**
- Input: Structured confirmation payload via api-q7v1.
- Process: Send HTTP request to backend endpoint (api-m5g7).
- Output: HTTP request with claim_id, status, source.
- Error: If network fails, show error notification and allow up to 2 retries before final failure.

### Test
`frontend/api_contracts/__tests__/confirmTruthCheck.test.ts`

- Reachability:
  - Mock `fetch` success (200).
  - Call `confirmTruthCheck(payload)`.
  - Assert correct POST to `/api/truth-checks/confirm`.

- TypeInvariant:
  - Assert request body matches `ConfirmTruthCheckRequest`.
  - Assert parsed response matches:
    ```ts
    { claim_id: string; status: "confirmed" | "denied"; source: string }
    ```

- ErrorConsistency:
  - Mock network failure.
  - Assert retries up to 2 times.
  - After 3rd failure, returns error state.
  - Component displays final failure message.

### Implementation

- `frontend/api_contracts/confirmTruthCheck.ts`
  - Typed function using `fetch`.
  - Retry loop (max 3 attempts total).
  - Zod schema for response validation.

---

## Step 3: Handle confirmation request - [x] Complete

**From path spec:**
- Input: HTTP request received by endpoint (api-m5g7).
- Process: Delegate to request handler (api-n8k2); validate required fields; forward normalized command to service (db-h2s4).
- Output: Validated command passed to service layer.
- Error: Missing/invalid fields → structured error (db-l1c3).

### Test
`backend/endpoints/__tests__/confirmTruthCheckRoute.test.ts`

- Reachability:
  - POST valid body.
  - Assert handler invoked with normalized command.

- TypeInvariant:
  - Zod schema validation for request body.
  - Assert handler receives `{ claim_id: string; status: "confirmed"|"denied"; source: string }`.

- ErrorConsistency:
  - POST missing `status`.
  - Assert 400 with structured error:
    ```ts
    { code: "TRUTH_CHECK_VALIDATION_ERROR", message: string }
    ```

### Implementation

- `route.ts`
  - Parse JSON.
  - Validate with Zod.
  - Call `ConfirmTruthCheckHandler.handle()`.
  - Catch and map errors from `TruthCheckErrors`.

- `TruthCheckErrors.ts`
  - `ValidationError`
  - `PersistenceError`

---

## Step 4: Persist truth check entry - [x] Complete

**From path spec:**
- Input: Validated command (claim_id, status, source).
- Process: Service (db-h2s4) calls DAO (db-d3w8) to create truth_checks record in data structure (db-f8n5).
- Output: Persisted record with stored status and source.
- Error: DB write fails → persistence error (db-l1c3).

### Test
`backend/services/__tests__/TruthCheckService.test.ts`

- Reachability:
  - Mock DAO success.
  - Call service.
  - Assert DAO.create called with correct fields.
  - Assert returned record contains persisted status + source.

- TypeInvariant:
  - Assert returned object matches `TruthCheck` structure:
    ```ts
    {
      id: string;
      claim_id: string;
      status: "confirmed" | "denied";
      source: string;
      created_at: string;
    }
    ```

- ErrorConsistency:
  - Mock DAO throws DB error.
  - Assert service throws `PersistenceError`.

### Implementation

- `TruthCheck.ts` (data structure)
  - Define TypeScript type + DB mapping.
  - Supabase migration: `truth_checks` table.

- `TruthCheckDAO.ts`
  - `create(data)` → insert into Supabase.

- `TruthCheckService.ts`
  - Orchestrates DAO call.
  - Maps DB exceptions to `PersistenceError`.

---

## Step 5: Return updated status to frontend - [x] Complete

**From path spec:**
- Input: Successful persistence result.
- Process: Endpoint returns success response; frontend updates UI state.
- Output: UI displays Confirmed or Denied.
- Error: Response parsing fails → log error and show generic failure message.

### Test
Frontend integration test:
`frontend/components/__tests__/ConfirmMetricClaim.integration.test.tsx`

- Reachability:
  - Mock successful API response.
  - Submit Y.
  - Assert UI displays “Confirmed”.

- TypeInvariant:
  - Assert displayed status strictly matches response status.

- ErrorConsistency:
  - Mock malformed JSON response.
  - Assert error logged.
  - Assert generic failure message shown.

### Implementation

- Component updates local state with response.
- Catch JSON/Zod parsing errors.
- Use frontend logging (`cfg-r3d7`).

---

## Terminal Condition

**Integration Test (E2E – Playwright)**
`e2e/confirm-metric-claim.spec.ts`

Flow:
1. Render metric claim.
2. Select Y.
3. Submit.
4. Assert:
   - UI shows “Confirmed”.
   - Database contains truth_checks row with:
     - correct `claim_id`
     - `status = confirmed`
     - correct `source`

Also test Denied path.

This proves:
- Reachability: trigger → UI → API → DB → UI.
- TypeInvariant: consistent types across layers.
- ErrorConsistency: validation, network, and DB failures yield structured error states.

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/297-confirm-metric-claim-truth-check.md`
- Gate 1: F-VERIFY-CLAIMS acceptance criterion 1
- TLA+ spec: `frontend/artifacts/tlaplus/297-confirm-metric-claim-truth-check/ConfirmMetricClaimTruthCheck.tla`
