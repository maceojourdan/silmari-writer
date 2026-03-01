# trigger-sms-follow-up-on-answer-finalization TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/335-trigger-sms-follow-up-on-answer-finalization.md

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

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

# Step 1: Detect Finalize Completion Event

**From path spec:**
- Input: Finalize completion event from mq-r4z8 including answer ID and user preferences from db-f8n5.
- Process: Evaluate context to determine if SMS follow-up is enabled.
- Output: Decision + validated answer ID + target phone number.
- Error: If preference or phone invalid/missing → validation error via cfg-j9w2.

---

## Test (`backend/services/__tests__/step1-detect-finalize.test.ts`)

**Reachability**
- Given finalize event `{ answerId, userId, smsOptIn: true, phoneNumber: '+15551234567' }`
- When `detectFinalizeCompletion(event)` is called
- Assert `{ shouldSend: true, answerId, phoneNumber }`

**TypeInvariant**
- Assert returned object conforms to `DetectFinalizeResult` Zod schema.

**ErrorConsistency**
- Case 1: `smsOptIn: false` → returns `{ shouldSend: false }`
- Case 2: `smsOptIn: true` but missing/invalid phone → throws `ValidationError` from `ValidationErrors.ts`.

---

## Implementation (`TriggerSmsFollowUpService.ts`)

- Define Zod schema for FinalizeEvent.
- Validate phone format.
- Return decision object.
- Throw `ValidationError.MISSING_PHONE_NUMBER` where applicable.

---

# Step 2: Load Answer and Contact Data

**From path spec:**
- Input: Answer ID and user ID.
- Process: Retrieve finalized answer and phone.
- Output: Structured payload `{ answerSummary, phoneNumber }`.
- Error: Not found or DB failure → domain error from db-l1c3.

---

## Test (`backend/services/__tests__/step2-load-data.test.ts`)

Mock `AnswerDAO` and `UserDAO`.

**Reachability**
- Given valid IDs
- When `loadAnswerAndContact(answerId, userId)`
- Assert structured payload returned.

**TypeInvariant**
- Assert payload matches `SmsPayloadSchema`.

**ErrorConsistency**
- If AnswerDAO returns null → throw `SmsErrors.ANSWER_NOT_FOUND`.
- If DB throws → map to `SmsErrors.DATABASE_FAILURE`.

---

## Implementation

- Implement DAO methods using Supabase client.
- Map null → domain error.
- Extract answer summary.

---

# Step 3: Compose SMS Follow-up Message

**From path spec:**
- Input: Answer summary + context.
- Process: Transform into SMS string within length constraints.
- Output: Validated SMS payload.
- Error: Length/validation failure → cfg-j9w2 validation error.

---

## Test (`backend/services/__tests__/step3-compose-sms.test.ts`)

**Reachability**
- Given valid summary
- When `composeSmsMessage(payload)`
- Assert returned `{ message: string }`.

**TypeInvariant**
- Assert message is string and ≤ 160 chars.

**ErrorConsistency**
- If summary produces >160 chars → throw `ValidationError.SMS_TOO_LONG`.

---

## Implementation

- Implement deterministic template function.
- Enforce max length constant.
- Throw shared validation error if exceeded.

---

# Step 4: Send SMS via External Provider

**From path spec:**
- Input: SMS payload + phone + provider config.
- Process: Call external API.
- Output: Delivery response.
- Error: Retry up to 3 times on transient; log persistent failure.

---

## Test (`backend/services/__tests__/step4-send-sms.test.ts`)

Mock Twilio SDK.

**Reachability**
- Provider returns success → assert `{ status: 'sent' }`.

**TypeInvariant**
- Assert response matches `SmsDeliveryResponse` schema.

**ErrorConsistency**
- Transient error twice then success → assert 3 calls made.
- Always failing → assert:
  - 3 attempts
  - `SmsErrors.PROVIDER_FAILURE` thrown
  - `SmsLogger.error` called.

---

## Implementation

- Load config from `SmsProviderSettings`.
- Implement retry loop (max 3) with exponential backoff.
- Log each attempt.

---

# Step 5: Record SMS Dispatch Result

**From path spec:**
- Input: Delivery response + answer ID.
- Process: Persist SMS record + audit log.
- Output: Stored record + log entry.
- Error: Persistence failure → critical log + operational alert.

---

## Test (`backend/services/__tests__/step5-record-result.test.ts`)

Mock `SmsFollowUpDAO`.

**Reachability**
- On success response
- Assert record stored and logger.info called.

**TypeInvariant**
- Assert stored entity matches `SmsFollowUpRecord` schema.

**ErrorConsistency**
- DAO throws → assert:
  - `SmsLogger.critical` called
  - Error re-thrown as `SmsErrors.PERSISTENCE_FAILURE`.

---

## Implementation

- Insert row into `sms_follow_ups` table.
- Log status.
- Wrap DB failure.

---

# Terminal Condition

## Integration Test
`backend/services/__tests__/trigger-sms-follow-up.integration.test.ts`

Scenario:
- Finalize event with smsOptIn true and valid phone.
- Mock DB + provider success.
- Call `handleFinalizeEvent(event)`.

Assertions:
- SMS sent once.
- SMS follow-up record persisted.
- Success log emitted.
- Final returned state: `{ status: 'completed' }`.

This proves Reachability from trigger → terminal success.

---

# Feedback Loop Test (Retry Behavior)

Integration test where:
- First 2 provider attempts throw transient error.
- 3rd succeeds.

Assert:
- Exactly 3 attempts.
- Final persisted status = success.
- Backoff timing function invoked.

---

# References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/335-trigger-sms-follow-up-on-answer-finalization.md
- Gate 1 Requirement: F-FINALIZE-EXPORT (SMS trigger on finalize)
- INT-SMS requirement
