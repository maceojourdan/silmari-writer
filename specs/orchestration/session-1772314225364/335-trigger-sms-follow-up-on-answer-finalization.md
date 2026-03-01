# PATH: trigger-sms-follow-up-on-answer-finalization

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

The finalize answer process chain completes for an answer where the user has opted in to SMS follow-up.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `mq-r4z8` | backend_process_chain | Emits the finalize completion event that triggers the SMS follow-up path. |
| `db-f8n5` | data_structure | Stores answer entities and user SMS opt-in and phone number fields. |
| `db-d3w8` | data_access_object | Retrieves and persists answer and SMS follow-up records. |
| `db-l1c3` | backend_error_definitions | Defines domain-specific errors for missing data and SMS dispatch failures. |
| `cfg-j9w2` | shared_error_definitions | Provides shared validation error types for message composition and preference checks. |
| `cfg-m2z6` | backend_settings | Supplies SMS provider configuration such as API keys and sender ID. |
| `cfg-q9c5` | backend_logging | Records SMS dispatch attempts, retries, and final status for observability. |

## Steps

1. **Detect Finalize Completion Event**
   - Input: Finalize operation completion event from mq-r4z8 (backend_process_chain) including answer identifier and user preferences from db-f8n5 (data_structure).
   - Process: Evaluate the completed finalize context to determine whether SMS follow-up is enabled for the associated user and answer.
   - Output: A decision to trigger SMS follow-up along with validated answer ID and target phone number.
   - Error: If user preference or phone number is missing or invalid, abort SMS trigger and record a validation error via cfg-j9w2 (shared_error_definitions).

2. **Load Answer and Contact Data**
   - Input: Answer ID and user ID from previous step, using db-d3w8 (data_access_object) and db-f8n5 (data_structure).
   - Process: Retrieve finalized answer details and the configured phone number required for SMS follow-up.
   - Output: Structured payload containing answer summary and destination phone number.
   - Error: If database retrieval fails or records are not found, return a domain error defined in db-l1c3 (backend_error_definitions) and stop SMS processing.

3. **Compose SMS Follow-up Message**
   - Input: Answer summary and contextual data, formatted according to shared rules.
   - Process: Transform answer data into an SMS-ready message string that complies with formatting and length constraints.
   - Output: Validated SMS message payload ready for external delivery.
   - Error: If transformation fails validation (e.g., message exceeds allowed length), raise a validation error using cfg-j9w2 (shared_error_definitions) and abort sending.

4. **Send SMS via External Provider**
   - Input: SMS message payload and destination phone number, provider configuration from cfg-m2z6 (backend_settings).
   - Process: Invoke an external SMS gateway API to dispatch the follow-up message to the configured phone number.
   - Output: Delivery response indicating success or failure.
   - Error: On transient provider errors, retry up to 3 times; on persistent failure, log error using cfg-q9c5 (backend_logging) and classify under db-l1c3 (backend_error_definitions).

5. **Record SMS Dispatch Result**
   - Input: Delivery response and associated answer ID.
   - Process: Persist SMS dispatch outcome and write an audit log entry for monitoring and traceability.
   - Output: Stored SMS follow-up record and visible log entry confirming dispatch status.
   - Error: If persistence fails, log critical error via cfg-q9c5 (backend_logging) and surface operational alert for manual review.

## Terminal Condition

An SMS follow-up message is successfully sent to the configured phone number and a confirmation is logged, visible in system logs or admin monitoring.

## Feedback Loops

If SMS delivery fails due to a transient provider error, retry up to 3 times with exponential backoff before marking the attempt as failed and logging a final error.
