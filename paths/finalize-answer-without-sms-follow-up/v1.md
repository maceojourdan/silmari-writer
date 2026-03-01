# PATH: finalize-answer-without-sms-follow-up

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1

## Trigger

Backend finalize process for an answer completes and the associated user has not opted in to SMS follow-up.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `mq-r4z8` | backend_process_chain | Triggers and completes the finalize workflow. |
| `db-d3w8` | data_access_object | Retrieves answer and user SMS preference from persistence. |
| `db-f8n5` | data_structure | Represents answer and user preference schema. |
| `db-j6x9` | backend_verifier | Validates finalized status and SMS opt-in condition. |
| `db-h2s4` | service | Orchestrates post-finalization logic and SMS decision. |
| `db-l1c3` | backend_error_definitions | Defines errors for retrieval, validation, and persistence failures. |
| `cfg-q9c5` | backend_logging | Logs malformed context or unintended SMS dispatch attempts. |

## Steps

1. **Receive finalize completion event**
   - Input: Finalize completion signal from backend_process_chain (mq-r4z8) including answer identifier.
   - Process: Capture the completion of the finalize process and pass the answer identifier to the responsible backend service for post-finalization actions.
   - Output: Finalize completion context containing answer ID ready for service evaluation.
   - Error: If finalize context is missing or malformed, log via backend_logging (cfg-q9c5) and abort SMS evaluation without retry.

2. **Load answer and user preference**
   - Input: Answer ID from finalize context; data_access_object (db-d3w8) and data_structure (db-f8n5).
   - Process: Retrieve the finalized answer and the associated user's SMS follow-up preference from persistent storage.
   - Output: Answer entity with finalized status and user SMS opt-in flag.
   - Error: If answer or user preference cannot be retrieved, raise appropriate error from backend_error_definitions (db-l1c3) and halt SMS follow-up processing.

3. **Evaluate SMS follow-up eligibility**
   - Input: Answer entity with finalized status and user SMS opt-in flag; backend_verifier (db-j6x9).
   - Process: Verify that the answer is finalized and evaluate the user's SMS opt-in flag to determine eligibility for SMS follow-up.
   - Output: Eligibility decision indicating that SMS follow-up is not permitted.
   - Error: If verification fails due to invalid state, return validation error and prevent any SMS dispatch attempt.

4. **Bypass SMS dispatch**
   - Input: Eligibility decision indicating SMS not permitted; backend service (db-h2s4).
   - Process: Skip invocation of any SMS sending mechanism and ensure no SMS dispatch request is created or queued.
   - Output: Confirmed absence of SMS dispatch action or message queue entry.
   - Error: If an SMS dispatch is inadvertently triggered, log as a high-severity issue via backend_logging (cfg-q9c5) and suppress the dispatch before it is sent.

5. **Complete finalize workflow without SMS**
   - Input: Confirmed absence of SMS dispatch; backend_process_chain (mq-r4z8).
   - Process: Conclude the finalize workflow, persisting any non-SMS-related finalization side effects.
   - Output: Answer remains finalized in the system with no SMS sent and no SMS record created.
   - Error: If persistence of finalization state fails, raise error from backend_error_definitions (db-l1c3) and mark workflow as failed without sending SMS.

## Terminal Condition

The answer is marked as finalized and no SMS message is sent to the user, with no SMS dispatch record created.

## Feedback Loops

None — strictly linear.
