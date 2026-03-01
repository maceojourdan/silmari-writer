# PATH: followup-sms-for-uncertain-claim

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

FOLLOWUP_SMS execution pattern is triggered for a claim

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `mq-t2f7` | execution_pattern | Defines FOLLOWUP_SMS trigger conditions |
| `mq-u6j3` | middleware_process_chain | Routes FOLLOWUP_SMS event through middleware stages |
| `mq-r4z8` | backend_process_chain | Executes ordered backend operations for SMS follow-up |
| `db-d3w8` | data_access_object | Retrieves and persists claim and user data |
| `db-f8n5` | data_structure | Represents claim entity including truth_checks and opt-in fields |
| `db-h2s4` | service | Orchestrates SMS sending and business logic |
| `db-b7r2` | processor | Processes structured reply into domain update |
| `db-l1c3` | backend_error_definitions | Defines backend error responses for failures |
| `api-m5g7` | endpoint | Receives inbound SMS webhook |
| `api-n8k2` | request_handler | Transforms inbound HTTP request into internal processing call |
| `cfg-h5v9` | transformer | Parses and maps raw SMS reply into structured truth-check update |
| `cfg-m2z6` | backend_settings | Stores SMS provider configuration |
| `cfg-p4b8` | shared_logging | Logs trigger bypass and correlation errors |
| `cfg-q9c5` | backend_logging | Logs SMS send and persistence failures |
| `cfg-j9w2` | shared_error_definitions | Defines cross-layer error codes for webhook validation issues |

## Steps

1. **Trigger FOLLOWUP_SMS pattern**
   - Input: FOLLOWUP_SMS trigger evaluated by execution pattern (mq-t2f7) within middleware process chain (mq-u6j3)
   - Process: Detect that a claim event matches the FOLLOWUP_SMS pattern and forward it into the backend process chain for handling
   - Output: FOLLOWUP_SMS event with claim identifier dispatched to backend process chain (mq-r4z8)
   - Error: If trigger conditions are not met, pattern bypasses processing; no SMS is sent and event is logged via shared logging (cfg-p4b8)

2. **Validate claim eligibility**
   - Input: Claim identifier from process chain (mq-r4z8), claim and user data from data access object (db-d3w8) over data structure (db-f8n5)
   - Process: Load the claim and associated user preferences, verify that the claim status is uncertain and that the user has SMS opt-in set to true
   - Output: Eligibility decision and enriched claim context for SMS sending
   - Error: If claim not found or data access fails, return backend error (db-l1c3) and stop processing; if eligibility conditions fail, terminate path without sending SMS and log outcome

3. **Send follow-up SMS**
   - Input: Eligible claim context from previous step, backend service (db-h2s4), SMS provider configuration from backend settings (cfg-m2z6)
   - Process: Compose follow-up message referencing the uncertain claim and send SMS through external provider via service orchestration
   - Output: SMS send result (success or failure status)
   - Error: On provider failure, retry up to 3 times; after max retries, raise backend error (db-l1c3) and log failure via backend logging (cfg-q9c5)

4. **Receive SMS reply webhook**
   - Input: Incoming SMS reply delivered to backend endpoint (api-m5g7) and handled by request handler (api-n8k2)
   - Process: Validate and parse the inbound SMS reply, correlate it to the original claim using shared transformer (cfg-h5v9), and forward structured reply to processor (db-b7r2)
   - Output: Structured truth-check update request associated with the claim
   - Error: If reply cannot be correlated to a claim, respond with appropriate error from shared error definitions (cfg-j9w2) and log incident

5. **Update truth_checks record**
   - Input: Structured truth-check update request, data access object (db-d3w8), and claim data structure (db-f8n5)
   - Process: Persist the user’s reply into the claim’s truth_checks field and update claim status accordingly
   - Output: Updated claim record with modified truth_checks reflecting user response
   - Error: If persistence fails, return backend error (db-l1c3) and log via backend logging (cfg-q9c5)

## Terminal Condition

User receives a follow-up SMS about the uncertain claim and, after replying, the claim’s truth_checks record reflects the user’s response

## Feedback Loops

If SMS delivery fails, retry send up to 3 times with exponential backoff before logging final failure.
