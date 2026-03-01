# transition-to-verify-when-minimum-slots-filled TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/296-transition-to-verify-when-minimum-slots-filled.md

Tech Stack (Gate 2 – Option 1):
- Frontend: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- Backend: Next.js API Routes, TypeScript, Zod
- DB: Supabase (Postgres)

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/296-transition-to-verify-when-minimum-slots-filled.md`

From verification_results_json:
- Result: **ALL PROPERTIES PASSED**
- States: 26 found, 13 distinct
- Exit code: 0
- Properties: Reachability, TypeInvariant, ErrorConsistency

This TDD plan implements code-level tests that assert the same three properties per step.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/BehavioralQuestionForm.tsx` |
| ui-v3n6 | module | `frontend/modules/behavioralQuestion/module.ts` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/behavioralQuestionVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/evaluateBehavioralQuestion.ts` |
| api-m5g7 | endpoint | `frontend/app/api/behavioral-question/evaluate/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/BehavioralQuestionEvaluateHandler.ts` |
| db-h2s4 | service | `backend/services/BehavioralQuestionService.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/BehavioralQuestionMinimumSlotsVerifier.ts` |
| db-f8n5 | data_structure | `backend/data_structures/BehavioralQuestion.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/BehavioralQuestionDAO.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/BehavioralQuestionErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

---

## Step 1: Capture slot updates in UI ✅

**From path spec:**
- Input: User-entered values in form fields.
- Process: Update local component state for objective, actions, obstacles, outcome, role clarity.
- Output: Updated frontend draft state.
- Error: If malformed, ui-a4y1 flags field and prevents progression.

### Test (`frontend/components/__tests__/BehavioralQuestionForm.test.tsx`)

- [x] Reachability: render component → simulate user typing → assert module state updated.
- [x] TypeInvariant: assert state matches `BehavioralQuestionDraft` TypeScript interface.
- [x] ErrorConsistency: simulate malformed input (e.g., empty objective on blur) → verifier returns field error → component renders error and disables submit.

### Implementation

- [x] Define `BehavioralQuestionDraft` type.
- [x] Controlled inputs in `BehavioralQuestionForm.tsx`.
- [x] On change → update module state (`ui-v3n6`).
- [x] Integrate `behavioralQuestionVerifier.validateField()` for per-field validation.

---

## Step 2: Validate minimum slot requirements on frontend ✅

**From path spec:**
- Input: Current draft + rules from ui-a4y1.
- Process: Check objective present, ≥3 actions, ≥1 obstacle, outcome present, role clarity present.
- Output: Validation result (boolean + field errors).
- Error: If fails, attach field-level errors; no backend call.

### Test (`frontend/verifiers/__tests__/behavioralQuestionVerifier.test.ts`)

- [x] Reachability: call `validateMinimumSlots(validDraft)` → expect `isValid=true`.
- [x] TypeInvariant: assert return type `{ isValid: boolean; errors: Record<string,string> }`.
- [x] ErrorConsistency: call with 2 actions → expect `isValid=false`, `errors.actions` defined.
- [x] Assert that `evaluateBehavioralQuestion` API contract is NOT invoked when invalid (mock fetch, expect not called).

### Implementation

- [x] Implement `validateMinimumSlots(draft)` in `behavioralQuestionVerifier.ts`.
- [x] Enforce slot counts.
- [x] In module submit handler, short-circuit before API call if invalid.

---

## Step 3: Submit validation request to backend ✅

**From path spec:**
- Input: Valid draft via api-q7v1 calling api-m5g7 through api-n8k2.
- Process: Send draft to backend endpoint.
- Output: Structured backend evaluation request.
- Error: Network/endpoint error → shared_error_definitions cfg-j9w2; retry up to 5 times.

### Test (`frontend/api_contracts/__tests__/evaluateBehavioralQuestion.test.ts`)

- [x] Reachability: mock `fetch` 200 → call contract → assert POST to `/api/behavioral-question/evaluate` with structured body.
- [x] TypeInvariant: assert request body matches `BehavioralQuestionDraft`.
- [x] ErrorConsistency: mock 500 → expect `SharedErrors.NetworkError`; retry logic invoked ≤5 times; error banner rendered.

### Implementation

- [x] Implement typed function `evaluateBehavioralQuestion(draft)`.
- [x] Wrap fetch in retry loop (max 5).
- [x] Map non-2xx to `SharedErrors.NetworkError`.

---

## Step 4: Verify minimum slots and determine state transition ✅

**From path spec:**
- Input: Data handled by db-h2s4 and validated by db-j6x9.
- Process: Server-side re-validation; determine eligibility for VERIFY.
- Output: Decision result `{ eligible: true }`.
- Error: Validation fails → db-l1c3 error; no state change.

### Test (`backend/services/__tests__/BehavioralQuestionService.test.ts`)

- [x] Reachability: call `evaluateForVerify(validEntity)` → expect `{ eligible: true }`.
- [x] TypeInvariant: assert entity matches `BehavioralQuestion` schema (Zod).
- [x] ErrorConsistency: invalid entity (2 actions) → expect `MinimumSlotsNotMetError` from db-l1c3.

### Implementation

- [x] Define Zod schema in `BehavioralQuestion.ts`.
- [x] Implement `BehavioralQuestionMinimumSlotsVerifier.verify(entity)`.
- [x] Service method `evaluateForVerify` returns eligibility or throws typed error.

---

## Step 5: Persist state transition to VERIFY ✅

**From path spec:**
- Input: Eligibility decision + question entity.
- Process: Update status from DRAFT → VERIFY via DAO.
- Output: Persisted record with status VERIFY.
- Error: Persistence fails → db-l1c3 error; state unchanged.

### Test (`backend/data_access_objects/__tests__/BehavioralQuestionDAO.test.ts`)

- [x] Reachability: mock Supabase update → call `updateStatus(id, "VERIFY")` → expect returned entity with status VERIFY.
- [x] TypeInvariant: assert returned type `BehavioralQuestion`.
- [x] ErrorConsistency: mock DB failure → expect `PersistenceError`; verify original status remains DRAFT.

### Implementation

- [x] Implement DAO with Supabase client.
- [x] Wrap DB errors into `PersistenceError`.
- [x] Service orchestrates: if eligible → DAO.updateStatus.

---

## Step 6: Reflect VERIFY state in UI ✅

**From path spec:**
- Input: Successful backend response.
- Process: Update frontend state; re-render status indicator.
- Output: UI displays VERIFY badge/stepper.
- Error: UI state update fails → cfg-r3d7 logs; fallback refresh once.

### Test (`frontend/modules/__tests__/behavioralQuestionModule.test.tsx`)

- [x] Reachability: mock successful API → dispatch submit → expect status badge shows "VERIFY".
- [x] TypeInvariant: module state type includes `status: 'DRAFT' | 'VERIFY'`.
- [x] ErrorConsistency: simulate state update exception → expect `frontend_logging.error` called and refresh triggered once.

### Implementation

- [x] Extend module state with `status`.
- [x] On successful API response → set status to VERIFY.
- [x] Wrap state update in try/catch; log via `frontend/logging` and trigger one `router.refresh()`.

---

## Terminal Condition ✅

### Integration Test (`frontend/__tests__/transitionToVerify.integration.test.ts`)

- [x] Render full form.
- [x] Fill objective, 3 actions, 1 obstacle, outcome, role clarity.
- [x] Submit.
- [x] Mock backend success.
- [x] Assert:
  - [x] Backend endpoint called.
  - [x] DAO update invoked.
  - [x] UI badge shows VERIFY.

This proves Reachability from trigger → VERIFY badge.

---

## Feedback Loop Tests ✅

- [x] Simulate invalid submission attempts up to 5 times → allowed.
- [x] 6th invalid attempt → cooldown message shown; no backend call.

Test file: `frontend/modules/__tests__/behavioralQuestionRetry.test.ts`

---

## References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/296-transition-to-verify-when-minimum-slots-filled.md
- Gate 1: F-RECALL-LOOP (minimum slots → VERIFY)
- Verification results JSON (path_id: 296)
