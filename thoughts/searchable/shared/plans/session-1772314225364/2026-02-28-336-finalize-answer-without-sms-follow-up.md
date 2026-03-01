# finalize-answer-without-sms-follow-up TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/336-finalize-answer-without-sms-follow-up.md

---

## Verification (Phase 0)

The TLA+ model for this path passed all required properties.

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/336-finalize-answer-without-sms-follow-up.md`

Result (from verification_results_json):
- Status: `verified`
- Exit code: `0`
- Output: `Result: ALL PROPERTIES PASSED`
- States: `22 found, 11 distinct`
- Properties:
  - `Reachability`
  - `TypeInvariant`
  - `ErrorConsistency`

This TDD plan maps those properties directly to code-level tests.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| mq-r4z8 | backend_process_chain | `backend/process_chains/FinalizeProcessChain.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/AnswerDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Answer.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/FinalizeEligibilityVerifier.ts` |
| db-h2s4 | service | `backend/services/FinalizeService.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/FinalizeErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |

Tech stack (Gate 2 – Option 1):
- Backend: Next.js API routes + TypeScript
- Testing: Vitest
- DB: Supabase (Postgres)

---

## Step 1: Receive finalize completion event

**From path spec:**
- Input: Finalize completion signal from backend_process_chain (mq-r4z8) including answer identifier.
- Process: Capture completion and pass answer identifier to backend service.
- Output: Finalize completion context containing answer ID.
- Error: If context missing/malformed, log via backend_logging (cfg-q9c5) and abort SMS evaluation without retry.

**Test** (`backend/process_chains/__tests__/FinalizeProcessChain.step1.test.ts`):
- Reachability: simulate finalize event `{ answerId: "a1" }`, assert service invoked with context.
- TypeInvariant: assert produced context matches `{ answerId: string }`.
- ErrorConsistency: call with `{}` or `null`, assert:
  - logger.error called
  - service not invoked
  - function returns early (e.g., `void` or aborted state)

**Implementation** (`backend/process_chains/FinalizeProcessChain.ts`):
- Export `handleFinalizeCompletion(event)`.
- Validate shape using Zod.
- On invalid: log via `backend/logging`, return.
- On valid: call `FinalizeService.evaluatePostFinalize(context)`.

---

## Step 2: Load answer and user preference

**From path spec:**
- Input: Answer ID; data_access_object (db-d3w8) and data_structure (db-f8n5).
- Process: Retrieve finalized answer and user SMS opt-in preference.
- Output: Answer entity with finalized status and user SMS opt-in flag.
- Error: If retrieval fails, raise error from backend_error_definitions (db-l1c3) and halt.

**Test** (`backend/services/__tests__/FinalizeService.step2.test.ts`):
- Reachability: mock `AnswerDAO.getById("a1")` returning `{ id, status: "FINALIZED", user: { smsOptIn: false } }`; assert returned entity.
- TypeInvariant: assert returned object conforms to `Answer` TypeScript interface.
- ErrorConsistency:
  - DAO returns null → expect `AnswerNotFoundError`.
  - DAO throws → expect mapped `PersistenceError` from `FinalizeErrors`.

**Implementation**:
- `AnswerDAO.getById(id)` queries Supabase.
- `Answer` structure includes `status: 'FINALIZED' | ...`, `user.smsOptIn: boolean`.
- Define errors in `FinalizeErrors.ts`.
- In `FinalizeService.evaluatePostFinalize`, fetch entity and throw typed errors if missing.

---

## Step 3: Evaluate SMS follow-up eligibility

**From path spec:**
- Input: Answer entity; backend_verifier (db-j6x9).
- Process: Verify finalized status and evaluate SMS opt-in flag.
- Output: Eligibility decision indicating SMS follow-up is not permitted.
- Error: If invalid state, return validation error and prevent SMS dispatch.

**Test** (`backend/verifiers/__tests__/FinalizeEligibilityVerifier.test.ts`):
- Reachability: pass `{ status: "FINALIZED", user.smsOptIn: false }`; expect `{ eligible: false }`.
- TypeInvariant: assert decision matches `{ eligible: boolean }`.
- ErrorConsistency:
  - status !== "FINALIZED" → expect `InvalidFinalizeStateError`.

**Implementation**:
- `FinalizeEligibilityVerifier.verify(answer)`:
  - if status !== FINALIZED → throw `InvalidFinalizeStateError`.
  - return `{ eligible: answer.user.smsOptIn === true }`.
- In this path, expect `eligible === false`.

---

## Step 4: Bypass SMS dispatch

**From path spec:**
- Input: Eligibility decision indicating SMS not permitted; backend service (db-h2s4).
- Process: Skip invocation of SMS sending mechanism; ensure no dispatch queued.
- Output: Confirmed absence of SMS dispatch action or queue entry.
- Error: If SMS dispatch inadvertently triggered, log high-severity and suppress.

**Test** (`backend/services/__tests__/FinalizeService.step4.test.ts`):
- Reachability: mock SMS client; with `{ eligible: false }`, assert `smsClient.send` NOT called.
- TypeInvariant: assert returned result `{ smsDispatched: false }`.
- ErrorConsistency:
  - Force internal branch that attempts send despite ineligible → assert:
    - logger.error called with high severity
    - send suppressed (not executed)

**Implementation**:
- Inject `SmsClient` into `FinalizeService`.
- If `eligible === false`, do not call SMS client.
- Guard clause: if logic ever attempts send while ineligible, log via `backend_logging` and abort.

---

## Step 5: Complete finalize workflow without SMS

**From path spec:**
- Input: Confirmed absence of SMS dispatch; backend_process_chain (mq-r4z8).
- Process: Conclude finalize workflow, persist non-SMS side effects.
- Output: Answer remains finalized; no SMS sent; no SMS record created.
- Error: If persistence fails, raise error and mark workflow failed without sending SMS.

**Test** (`backend/process_chains/__tests__/FinalizeProcessChain.step5.test.ts`):
- Reachability: simulate full flow; assert:
  - Answer.status === "FINALIZED"
  - No SMS record inserted (mock SMS table/DAO not called)
- TypeInvariant: assert returned workflow result `{ success: true }`.
- ErrorConsistency:
  - Mock persistence failure → expect `FinalizePersistenceError` and:
    - no SMS send attempt
    - workflow marked failed

**Implementation**:
- In `FinalizeService`, after Step 4:
  - Persist finalization metadata (e.g., export timestamp, KPI logging hook).
- Ensure transactional boundary: if persistence fails, throw typed error.
- `FinalizeProcessChain` catches and marks workflow failed.

---

## Terminal Condition

**Integration Test** (`backend/process_chains/__tests__/FinalizeWithoutSms.integration.test.ts`):

Scenario:
- Answer in DB with `status = FINALIZED`
- `user.smsOptIn = false`
- Trigger finalize completion event

Assertions:
- Full path executes without error
- No call to SMS client
- No SMS dispatch record created
- Answer remains `FINALIZED`
- Workflow result indicates success

This integration test proves:
- Reachability: trigger → terminal condition reachable
- TypeInvariant: types consistent across chain
- ErrorConsistency: no unintended SMS, correct handling of failures

---

## References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/336-finalize-answer-without-sms-follow-up.md
- Gate 1 Requirement: F-FINALIZE-EXPORT (acceptance criterion 5)
- verification_results_json (path_id: 336)
