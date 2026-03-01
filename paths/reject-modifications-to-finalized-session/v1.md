# PATH: reject-modifications-to-finalized-session

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User attempts to submit additional voice input or re-finalize a session that is already in FINALIZED state

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Captures user action to submit additional voice input or re-finalize session |
| `ui-a4y1` | frontend_verifier | Validates request payload before submission |
| `api-q7v1` | frontend_api_contract | Defines typed contract for modification endpoint |
| `api-m5g7` | endpoint | Receives HTTP request for session modification |
| `api-n8k2` | request_handler | Bridges endpoint request to backend service logic |
| `db-h2s4` | service | Orchestrates session state validation and business rules |
| `db-d3w8` | data_access_object | Retrieves StoryRecord and would persist changes if allowed |
| `db-f8n5` | data_structure | Represents StoryRecord entity including state field |
| `db-j6x9` | backend_verifier | Enforces rule that FINALIZED sessions are immutable |
| `db-l1c3` | backend_error_definitions | Defines domain errors such as session already finalized |

## Steps

1. **Submit modification request**
   - Input: User action in UI component (ui-w8p2) triggers frontend API contract (api-q7v1) call to backend endpoint (api-m5g7) with session identifier and action type (add voice input or finalize)
   - Process: The frontend sends a request to the backend endpoint requesting to append voice input or finalize the session
   - Output: HTTP request containing session ID and intended modification action delivered to backend endpoint
   - Error: If request payload is malformed, frontend_verifier (ui-a4y1) blocks submission and shows validation error

2. **Route request to handler**
   - Input: Incoming HTTP request received by endpoint (api-m5g7)
   - Process: Endpoint validates request shape and forwards it to the corresponding request handler (api-n8k2)
   - Output: Structured command object passed to backend processor layer
   - Error: If endpoint validation fails, backend_error_definitions (db-l1c3) are used to return a 4xx error response

3. **Load StoryRecord**
   - Input: Structured command containing session ID processed by service (db-h2s4)
   - Process: Service queries data_access_object (db-d3w8) to retrieve the StoryRecord from data_structure (db-f8n5)
   - Output: StoryRecord entity with current state (expected FINALIZED)
   - Error: If StoryRecord is not found, backend_error_definitions (db-l1c3) produce a not-found error response

4. **Verify session state**
   - Input: Loaded StoryRecord entity in FINALIZED state
   - Process: Service applies backend_verifier (db-j6x9) to check whether the StoryRecord state allows further modification; detects state is FINALIZED and modification is disallowed
   - Output: Validation failure indicating modification attempt on finalized session
   - Error: If verifier logic is missing for this rule, mark as [PROPOSED: Verifier rule enforcing immutability when state == FINALIZED]

5. **Reject modification and preserve state**
   - Input: Validation failure result and unchanged StoryRecord
   - Process: Service aborts modification flow, does not invoke any persistence update on data_access_object (db-d3w8), and maps the failure to a domain-specific error using backend_error_definitions (db-l1c3)
   - Output: Error response returned through endpoint (api-m5g7) indicating session already finalized; StoryRecord remains unchanged in FINALIZED state
   - Error: If error mapping fails, fallback to generic conflict error defined in backend_error_definitions (db-l1c3)

## Terminal Condition

User receives a rejection response indicating the session is already finalized, and the StoryRecord remains visibly unchanged in FINALIZED state

## Feedback Loops

None — strictly linear.
