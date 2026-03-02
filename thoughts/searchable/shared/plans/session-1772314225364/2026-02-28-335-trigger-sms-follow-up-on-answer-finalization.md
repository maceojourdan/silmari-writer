# trigger-sms-follow-up-on-answer-finalization TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/335-trigger-sms-follow-up-on-answer-finalization.md

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- [x] Reachability
- [x] TypeInvariant
- [x] ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/335-trigger-sms-follow-up-on-answer-finalization.md`

Stdout:
```
Path: trigger-sms-follow-up-on-answer-finalization
TLA+ spec: /home/maceo/wt/CodeWriter7/frontend-gate1-ui/frontend/artifacts/tlaplus/335-trigger-sms-follow-up-on-answer-finalization/TriggerSmsFollowUpOnAnswerFinalization.tla
TLC config: /home/maceo/wt/CodeWriter7/frontend-gate1-ui/frontend/artifacts/tlaplus/335-trigger-sms-follow-up-on-answer-finalization/TriggerSmsFollowUpOnAnswerFinalization.cfg
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
```

This TDD plan enforces the same properties at code level.

---

## Tech Stack (Gate 2)

Option 1 – Next.js (App Router) + API Routes + TypeScript + Supabase + Twilio SDK + Vitest.

Tests: Vitest (Node environment)  
Validation: Zod  

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| mq-r4z8 | backend_process_chain | `backend/process_chains/FinalizeProcessChain.ts` (event emitter) |
| db-f8n5 | data_structure | `backend/data_structures/Answer.ts`, `backend/data_structures/User.ts`, `backend/data_structures/SmsFollowUpRecord.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/AnswerDAO.ts`, `UserDAO.ts`, `SmsFollowUpDAO.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/SmsErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/ValidationErrors.ts` |
| cfg-m2z6 | backend_settings | `backend/settings/SmsProviderSettings.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/SmsLogger.ts` |

Primary orchestrator service:
`backend/services/TriggerSmsFollowUpService.ts`

---

# Step 1: Detect Finalize Completion Event ✅

**From path spec:**
- [x] Input: Finalize completion event from mq-r4z8 including answer ID and user preferences from db-f8n5.
- [x] Process: Evaluate context to determine if SMS follow-up is enabled.
- [x] Output: Decision + validated answer ID + target phone number.
- [x] Error: If preference or phone invalid/missing → validation error via cfg-j9w2.

---

## Test (`backend/services/__tests__/step1-detect-finalize.test.ts`) ✅

**Reachability**
- [x] Given finalize event `{ answerId, userId, smsOptIn: true, phoneNumber: '+15551234567' }`
- [x] When `detectFinalizeCompletion(event)` is called
- [x] Assert `{ shouldSend: true, answerId, phoneNumber }`

**TypeInvariant**
- [x] Assert returned object conforms to `DetectFinalizeResult` Zod schema.

**ErrorConsistency**
- [x] Case 1: `smsOptIn: false` → returns `{ shouldSend: false }`
- [x] Case 2: `smsOptIn: true` but missing/invalid phone → throws `ValidationError` from `ValidationErrors.ts`.

---

## Implementation (`TriggerSmsFollowUpService.ts`) ✅

- [x] Define Zod schema for FinalizeEvent.
- [x] Validate phone format.
- [x] Return decision object.
- [x] Throw `ValidationError.MISSING_PHONE_NUMBER` where applicable.

---

# Step 2: Load Answer and Contact Data ✅

**From path spec:**
- [x] Input: Answer ID and user ID.
- [x] Process: Retrieve finalized answer and phone.
- [x] Output: Structured payload `{ answerSummary, phoneNumber }`.
- [x] Error: Not found or DB failure → domain error from db-l1c3.

---

## Test (`backend/services/__tests__/step2-load-data.test.ts`) ✅

Mock `AnswerDAO` and `UserDAO`.

**Reachability**
- [x] Given valid IDs
- [x] When `loadAnswerAndContact(answerId, userId)`
- [x] Assert structured payload returned.

**TypeInvariant**
- [x] Assert payload matches `SmsPayloadSchema`.

**ErrorConsistency**
- [x] If AnswerDAO returns null → throw `SmsErrors.ANSWER_NOT_FOUND`.
- [x] If DB throws → map to `SmsErrors.DATABASE_FAILURE`.

---

## Implementation ✅

- [x] Implement DAO methods using Supabase client.
- [x] Map null → domain error.
- [x] Extract answer summary.

---

# Step 3: Compose SMS Follow-up Message ✅

**From path spec:**
- [x] Input: Answer summary + context.
- [x] Process: Transform into SMS string within length constraints.
- [x] Output: Validated SMS payload.
- [x] Error: Length/validation failure → cfg-j9w2 validation error.

---

## Test (`backend/services/__tests__/step3-compose-sms.test.ts`) ✅

**Reachability**
- [x] Given valid summary
- [x] When `composeSmsMessage(payload)`
- [x] Assert returned `{ message: string }`.

**TypeInvariant**
- [x] Assert message is string and ≤ 160 chars.

**ErrorConsistency**
- [x] If summary produces >160 chars → throw `ValidationError.SMS_TOO_LONG`.

---

## Implementation ✅

- [x] Implement deterministic template function.
- [x] Enforce max length constant.
- [x] Throw shared validation error if exceeded.

---

# Step 4: Send SMS via External Provider ✅

**From path spec:**
- [x] Input: SMS payload + phone + provider config.
- [x] Process: Call external API.
- [x] Output: Delivery response.
- [x] Error: Retry up to 3 times on transient; log persistent failure.

---

## Test (`backend/services/__tests__/step4-send-sms.test.ts`) ✅

Mock Twilio SDK.

**Reachability**
- [x] Provider returns success → assert `{ status: 'sent' }`.

**TypeInvariant**
- [x] Assert response matches `SmsDeliveryResponse` schema.

**ErrorConsistency**
- [x] Transient error twice then success → assert 3 calls made.
- [x] Always failing → assert:
  - [x] 3 attempts
  - [x] `SmsErrors.PROVIDER_FAILURE` thrown
  - [x] `SmsLogger.error` called.

---

## Implementation ✅

- [x] Load config from `SmsProviderSettings`.
- [x] Implement retry loop (max 3) with exponential backoff.
- [x] Log each attempt.

---

# Step 5: Record SMS Dispatch Result ✅

**From path spec:**
- [x] Input: Delivery response + answer ID.
- [x] Process: Persist SMS record + audit log.
- [x] Output: Stored record + log entry.
- [x] Error: Persistence failure → critical log + operational alert.

---

## Test (`backend/services/__tests__/step5-record-result.test.ts`) ✅

Mock `SmsFollowUpDAO`.

**Reachability**
- [x] On success response
- [x] Assert record stored and logger.info called.

**TypeInvariant**
- [x] Assert stored entity matches `SmsFollowUpRecord` schema.

**ErrorConsistency**
- [x] DAO throws → assert:
  - [x] `SmsLogger.critical` called
  - [x] Error re-thrown as `SmsErrors.PERSISTENCE_FAILURE`.

---

## Implementation ✅

- [x] Insert row into `sms_follow_ups` table.
- [x] Log status.
- [x] Wrap DB failure.

---

# Terminal Condition ✅

## Integration Test ✅
`backend/services/__tests__/trigger-sms-follow-up.integration.test.ts`

Scenario:
- [x] Finalize event with smsOptIn true and valid phone.
- [x] Mock DB + provider success.
- [x] Call `handleFinalizeEvent(event)`.

Assertions:
- [x] SMS sent once.
- [x] SMS follow-up record persisted.
- [x] Success log emitted.
- [x] Final returned state: `{ status: 'completed' }`.

This proves Reachability from trigger → terminal success.

---

# Feedback Loop Test (Retry Behavior) ✅

Integration test where:
- [x] First 2 provider attempts throw transient error.
- [x] 3rd succeeds.

Assert:
- [x] Exactly 3 attempts.
- [x] Final persisted status = success.
- [x] Backoff timing function invoked.

---

# References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/335-trigger-sms-follow-up-on-answer-finalization.md
- Gate 1 Requirement: F-FINALIZE-EXPORT (SMS trigger on finalize)
- INT-SMS requirement
