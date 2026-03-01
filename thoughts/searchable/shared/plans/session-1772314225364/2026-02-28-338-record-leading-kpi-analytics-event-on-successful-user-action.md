# record-leading-kpi-analytics-event-on-successful-user-action TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/338-record-leading-kpi-analytics-event-on-successful-user-action.md`

Tech stack: **Option 1 – Next.js (App Router) + TypeScript + Supabase (Postgres) + Vitest**

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- ✅ Reachability
- ✅ TypeInvariant
- ✅ ErrorConsistency

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/338-record-leading-kpi-analytics-event-on-successful-user-action.md
```

Stdout excerpt:
```
Result: ALL PROPERTIES PASSED
States: 26 found, 13 distinct, depth 0
```

This plan mirrors those properties as code-level test oracles.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/OnboardingStepOne.tsx` |
| ui-v3n6 | module | `frontend/modules/OnboardingModule.ts` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/OnboardingCompletionVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/CompleteOnboardingStep.ts` |
| api-m5g7 | endpoint | `backend/endpoints/CompleteOnboardingStepEndpoint.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/CompleteOnboardingStepHandler.ts` |
| db-b7r2 | processor | `backend/processors/OnboardingCompletionProcessor.ts` |
| db-h2s4 | service | `backend/services/OnboardingService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/OnboardingDao.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Onboarding.ts`, `AnalyticsEvent.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/BackendErrors.ts` |
| cfg-k3x7 | constant | `shared/constants/LeadingKpis.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |

---

## Step 1: User completes KPI-contributing action

**From path spec:**
- Input: User interaction within ui-w8p2 inside ui-v3n6.
- Process: Validate input and submit via api-q7v1.
- Output: Structured API request for onboarding step 1 completion.
- Error: If validation fails, prevent submission; no KPI event triggered.

### Test
`frontend/components/__tests__/OnboardingStepOne.test.tsx`

- **Reachability:**
  - Render component inside `OnboardingModule`.
  - Simulate valid completion.
  - Assert `CompleteOnboardingStep.request()` called with:
    ```ts
    { userId, step: 1, metadata }
    ```
- **TypeInvariant:**
  - Assert request matches TypeScript type `CompleteOnboardingStepRequest`.
- **ErrorConsistency:**
  - Provide invalid input.
  - Assert verifier blocks submission.
  - Assert API contract not called.

### Implementation
- `OnboardingCompletionVerifier.ts` using Zod schema.
- `CompleteOnboardingStep.ts` typed function wrapping `fetch`.
- Component calls verifier before contract.

---

## Step 2: Backend endpoint receives completion request

**From path spec:**
- Input: HTTP request via api-m5g7 → api-n8k2.
- Process: Validate structure and forward to processor.
- Output: Validated completion command.
- Error: Invalid structure/auth → db-l1c3 error; no KPI event recorded.

### Test
`backend/endpoints/__tests__/CompleteOnboardingStepEndpoint.test.ts`

- **Reachability:**
  - POST valid body.
  - Assert handler invokes `OnboardingCompletionProcessor.process()`.
- **TypeInvariant:**
  - Validate request parsed with Zod schema.
- **ErrorConsistency:**
  - Send malformed body.
  - Expect `400` with `BackendErrors.INVALID_REQUEST`.
  - Assert processor not invoked.

### Implementation
- Zod schema in handler.
- Error mapping from `BackendErrors.ts`.
- Next.js route handler returning typed JSON.

---

## Step 3: Business logic confirms successful action

**From path spec:**
- Input: Completion command in processor.
- Process: Verify eligibility, update onboarding state.
- Output: Persisted onboarding completion state.
- Error: Eligibility/persistence failure → db-l1c3 error; no KPI event.

### Test
`backend/processors/__tests__/OnboardingCompletionProcessor.step3.test.ts`

- **Reachability:**
  - Given eligible user.
  - Assert `OnboardingDao.updateOnboardingStep()` called.
- **TypeInvariant:**
  - Assert returned object matches `OnboardingCompletionResult` type.
- **ErrorConsistency:**
  - Mock DAO failure.
  - Expect `BackendErrors.PERSISTENCE_FAILED`.
  - Assert no analytics event creation attempted.

### Implementation
- `OnboardingService.isEligible(userId, step)`.
- DAO method updating `Onboarding` table.
- Processor orchestrates and returns typed result.

---

## Step 4: Construct leading KPI analytics event

**From path spec:**
- Input: Successful completion result + KPI identifier from cfg-k3x7.
- Process: Construct analytics event object.
- Output: Analytics event entity.
- Error: Missing KPI/metadata → db-l1c3 error; onboarding remains recorded.

### Test
`backend/processors/__tests__/OnboardingCompletionProcessor.step4.test.ts`

- **Reachability:**
  - After successful completion, assert event constructed with:
    - `kpiId === LeadingKpis.ONBOARDING_STEP_1`
    - `userId`
    - `timestamp`
    - `metadata.step === 1`
- **TypeInvariant:**
  - Assert matches `AnalyticsEvent` type.
- **ErrorConsistency:**
  - Remove KPI constant.
  - Expect `BackendErrors.KPI_IDENTIFIER_MISSING`.
  - Assert onboarding completion already persisted.

### Implementation
- `LeadingKpis.ts` exports `ONBOARDING_STEP_1`.
- Processor builds `AnalyticsEvent` object before persistence.

---

## Step 5: Persist analytics event

**From path spec:**
- Input: Analytics event entity via DAO.
- Process: Persist to analytics table.
- Output: Stored analytics event record.
- Error: DB write fails → error logged via cfg-q9c5; onboarding remains successful.

### Test
`backend/data_access_objects/__tests__/AnalyticsEventPersistence.test.ts`

- **Reachability:**
  - Call `OnboardingDao.insertAnalyticsEvent()`.
  - Assert row inserted in `analytics_events` table.
- **TypeInvariant:**
  - Assert DB row matches `AnalyticsEvent` schema.
- **ErrorConsistency:**
  - Simulate DB failure.
  - Assert `backend_logging.error()` called.
  - Assert processor returns success for onboarding but flags analytics failure.

### Implementation
- `AnalyticsEvent.ts` schema definition.
- DAO method inserting into Supabase.
- Structured logging on catch.

---

## Step 6: Return success response to user

**From path spec:**
- Input: Successful completion + analytics confirmation.
- Process: Handler returns success response.
- Output: UI confirmation.
- Error: Response failure → generic frontend error; idempotency prevents duplicates.

### Test
`backend/endpoints/__tests__/CompleteOnboardingStepResponse.test.ts`

- **Reachability:**
  - Full request → expect `200 { status: "completed" }`.
- **TypeInvariant:**
  - Assert response matches `CompleteOnboardingStepResponse` type.
- **ErrorConsistency:**
  - Simulate network failure on frontend.
  - Assert UI shows generic error.
  - Re-submit → processor idempotency prevents duplicate analytics event.

### Implementation
- Handler returns typed success payload.
- Processor enforces idempotency (check if step already completed before insert).

---

## Terminal Condition

### Integration Test
`backend/__tests__/RecordLeadingKpiIntegration.test.ts`

Exercise full path:
1. Simulate frontend POST.
2. Assert:
   - Onboarding table shows step 1 completed.
   - `analytics_events` contains record with:
     - Correct `kpiId`
     - Valid timestamp
     - Correct `userId`
     - Metadata `{ step: 1 }`
3. Assert frontend receives confirmation.

This proves:
- ✅ Reachability (trigger → terminal)
- ✅ TypeInvariant (typed contracts at each boundary)
- ✅ ErrorConsistency (all defined failure branches tested)

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/338-record-leading-kpi-analytics-event-on-successful-user-action.md`
- Gate 1: `NF-KPI-LOGGING`
- Shared constants: `LeadingKpis`
- Backend error definitions: `BackendErrors`
