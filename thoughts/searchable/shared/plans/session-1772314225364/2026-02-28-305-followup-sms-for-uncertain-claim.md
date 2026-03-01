# followup-sms-for-uncertain-claim TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/305-followup-sms-for-uncertain-claim.md`

Tech stack: **Option 1 – Fastest Path** (Next.js App Router, API Routes, TypeScript, Supabase, Twilio SDK, Vitest)

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- ✅ Reachability
- ✅ TypeInvariant
- ✅ ErrorConsistency

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/305-followup-sms-for-uncertain-claim.md
```

Verification output:
```
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct
```

All three properties are satisfied at the model level. The following tests replicate those guarantees at code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| mq-t2f7 | execution_pattern | `middleware/execution_patterns/FollowupSmsPattern.ts` |
| mq-u6j3 | middleware_process_chain | `middleware/process_chains/FollowupMiddlewareChain.ts` |
| mq-r4z8 | backend_process_chain | `backend/process_chains/FollowupSmsProcessChain.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/ClaimDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Claim.ts` |
| db-h2s4 | service | `backend/services/SmsFollowupService.ts` |
| db-b7r2 | processor | `backend/processors/TruthCheckReplyProcessor.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/BackendErrors.ts` |
| api-m5g7 | endpoint | `backend/endpoints/SmsWebhookEndpoint.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/SmsWebhookHandler.ts` |
| cfg-h5v9 | transformer | `shared/transformers/SmsReplyTransformer.ts` |
| cfg-m2z6 | backend_settings | `backend/settings/SmsProviderSettings.ts` |
| cfg-p4b8 | shared_logging | `shared/logging/index.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/WebhookErrors.ts` |

---

## Step 1: Trigger FOLLOWUP_SMS pattern ✅

**From path spec:**
- Input: FOLLOWUP_SMS trigger evaluated by execution pattern (mq-t2f7) within middleware process chain (mq-u6j3)
- Process: Detect match and forward to backend process chain
- Output: FOLLOWUP_SMS event with claim identifier dispatched to mq-r4z8
- Error: If trigger conditions not met → bypass + log via cfg-p4b8

### Test ✅
`server/execution_patterns/__tests__/FollowupSmsPattern.test.ts` — 9 tests passing

- [x] **Reachability**: Given event `{ type: 'FOLLOWUP_SMS', claimId }`, when pattern evaluates → backend chain called with `{ claimId }`
- [x] **TypeInvariant**: Assert output type `FollowupSmsEvent` contains `claimId: string`
- [x] **ErrorConsistency**: Given non-matching event → backend chain not called, shared logger invoked with `pattern_bypass`

### Implementation ✅
`server/execution_patterns/FollowupSmsPattern.ts`
- [x] Export `evaluate(event)`
- [x] If `event.type === 'FOLLOWUP_SMS'` → call `FollowupSmsProcessChain.start({ claimId })`
- [x] Else → log via shared logger and return `BYPASS`

---

## Step 2: Validate claim eligibility ✅

**From path spec:**
- Input: claimId + DAO (db-d3w8) + Claim structure (db-f8n5)
- Process: Load claim + verify `status === 'UNCERTAIN'` and `smsOptIn === true`
- Output: Eligibility decision + enriched claim context
- Error: If not found/DAO failure → backend error; if ineligible → terminate + log

### Test ✅
`server/process_chains/__tests__/FollowupSmsProcessChain.step2.test.ts` — 10 tests passing

- [x] **Reachability**: Given valid claim in DB (UNCERTAIN + opt-in true) → returns `{ eligible: true, claim }`
- [x] **TypeInvariant**: Assert returned object matches `EligibleClaimContext` type
- [x] **ErrorConsistency (DAO fail)**: Mock DAO throw → expect `BackendErrors.CLAIM_LOAD_FAILED`
- [x] **ErrorConsistency (ineligible)**: Claim with `smsOptIn=false` → result `{ eligible: false }` and no SMS call

### Implementation ✅
- [x] `ClaimDAO.findById(claimId)`
- [x] Define `Claim` type with `truth_checks`, `status`, `smsOptIn`
- [x] In process chain, guard eligibility
- [x] Throw `BackendErrors.CLAIM_LOAD_FAILED` on DAO exception

---

## Step 3: Send follow-up SMS ✅

**From path spec:**
- Input: Eligible claim context + SmsFollowupService + cfg-m2z6
- Process: Compose message + send via Twilio SDK
- Output: SMS send result
- Error: Retry up to 3 times; after max → backend error + backend log

### Test ✅
`server/services/__tests__/SmsFollowupService.test.ts` — 12 tests passing

- [x] **Reachability**: Given eligible claim → SMS client called once, returns `{ status: 'sent' }`
- [x] **TypeInvariant**: Assert result type `SmsSendResult` (`status: 'sent' | 'failed'`)
- [x] **ErrorConsistency (retry)**: Mock provider fail twice then succeed → service attempts 3 times, returns success
- [x] **ErrorConsistency (max fail)**: Mock provider always fail → after 3 attempts throw `BackendErrors.SMS_SEND_FAILED` and backend logger called

### Implementation ✅
- [x] `SmsProviderSettings` loads credentials
- [x] `SmsFollowupService.sendFollowup(claim)`
- [x] Retry loop (max=3) with exponential backoff (mockable timer)
- [x] Use `backend/logging` on final failure

---

## Step 4: Receive SMS reply webhook ✅

**From path spec:**
- Input: HTTP POST to endpoint (api-m5g7)
- Process: Validate request, parse reply, correlate to claim via transformer, forward to processor
- Output: Structured truth-check update request
- Error: If cannot correlate → shared error + log

### Test ✅
`server/request_handlers/__tests__/SmsWebhookHandler.test.ts` — 9 tests passing

- [x] **Reachability**: POST valid Twilio payload → handler returns 200 and calls `TruthCheckReplyProcessor.process(structuredUpdate)`
- [x] **TypeInvariant**: Assert transformer returns `TruthCheckUpdateRequest` with `claimId` + `verdict`
- [x] **ErrorConsistency**: Invalid/missing claim correlation → response 400 with `WebhookErrors.CLAIM_NOT_FOUND`, logged

### Implementation ✅
- [x] Next.js API route `/api/sms/webhook`
- [x] `SmsWebhookHandler.handle(req)`
- [x] `SmsReplyTransformer.parse(payload)`
- [x] On correlation failure → throw `WebhookErrors.CLAIM_NOT_FOUND`

---

## Step 5: Update truth_checks record ✅

**From path spec:**
- Input: Structured truth-check update + DAO + Claim structure
- Process: Persist reply into `truth_checks`, update claim status
- Output: Updated claim record
- Error: Persistence fail → backend error + backend log

### Test ✅
`server/processors/__tests__/TruthCheckReplyProcessor.test.ts` — 9 tests passing

- [x] **Reachability**: Given structured update → DAO updates claim → returns updated claim with modified `truth_checks`
- [x] **TypeInvariant**: Assert updated claim matches `Claim` type and `truth_checks` reflects verdict
- [x] **ErrorConsistency**: DAO throws → expect `BackendErrors.TRUTH_CHECK_PERSIST_FAILED` and backend logger invoked

### Implementation ✅
- [x] `TruthCheckReplyProcessor.process(update)`
- [x] `ClaimDAO.updateTruthCheck(claimId, verdict)`
- [x] Update claim `status` accordingly
- [x] Wrap DAO errors in backend error definition

---

## Terminal Condition ✅

### Integration Test ✅
`server/__tests__/followupSmsFlow.integration.test.ts` — 16 tests passing

- [x] Seed claim: `status=’UNCERTAIN’`, `smsOptIn=true`
- [x] Trigger FOLLOWUP_SMS event
- [x] Assert:
  - [x] SMS send invoked
  - [x] Simulate webhook reply
  - [x] Final claim record has updated `truth_checks`
  - [x] Claim status updated accordingly

**Asserts Reachability** ✅: Full trigger → Step1→Step2→Step3→Step4→Step5

**Asserts TypeInvariant** ✅: All intermediate DTOs match declared TS interfaces

**Asserts ErrorConsistency** ✅: Simulate provider + DAO failures and assert defined backend/shared errors

Terminal condition satisfied when:
> User receives follow-up SMS and claim’s truth_checks reflects user response.

---

## References
- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/305-followup-sms-for-uncertain-claim.md`
- Gate 1 Requirement: `INT-SMS`
- Gate 2 Stack: Option 1 – Next.js + Supabase + Twilio
