# PATH: reject-duplicate-session-initialization

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User or frontend triggers the session initialization endpoint while a session with ResumeObject, JobObject, and QuestionObject is already active

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `api-m5g7` | endpoint | Receives session initialization HTTP request |
| `api-n8k2` | request_handler | Bridges endpoint to backend service and maps errors to HTTP responses |
| `db-h2s4` | service | Orchestrates session initialization business logic |
| `db-d3w8` | data_access_object | Retrieves current session state from persistence |
| `db-f8n5` | data_structure | Represents session entity with active/inactive status |
| `db-j6x9` | backend_verifier | Enforces rule that only one active session may exist |
| `db-l1c3` | backend_error_definitions | Defines standardized error codes and messages such as SESSION_ALREADY_ACTIVE |
| `api-q7v1` | frontend_api_contract | Defines typed error response consumed by frontend |

## Steps

1. **Receive session initialization request**
   - Input: HTTP request to backend API endpoint (api-m5g7) routed to request handler (api-n8k2)
   - Process: Accept and route the session initialization request containing ResumeObject, JobObject, and QuestionObject to the appropriate backend processor flow
   - Output: Structured session initialization command passed to backend service layer (db-h2s4)
   - Error: If request payload is malformed or missing required objects, return validation error defined in backend_error_definitions (db-l1c3)

2. **Check for existing active session**
   - Input: Session initialization command and current session state retrieved via data access object (db-d3w8) from session data structure (db-f8n5)
   - Process: Determine whether there is an existing active session that has not been ended
   - Output: Boolean result indicating whether an active session already exists
   - Error: If session state cannot be retrieved due to persistence failure, return system error defined in backend_error_definitions (db-l1c3)

3. **Validate session uniqueness constraint**
   - Input: Active session existence flag and session initialization command
   - Process: Apply business rule via backend verifier (db-j6x9) that prohibits initializing a new session when one is already active
   - Output: Validation result indicating rejection due to already active session
   - Error: If validation fails because a session is already active, generate domain error 'SESSION_ALREADY_ACTIVE' from backend_error_definitions (db-l1c3)

4. **Return error response to client**
   - Input: Domain error 'SESSION_ALREADY_ACTIVE' from service layer (db-h2s4)
   - Process: Transform domain error into standardized HTTP error response through request handler (api-n8k2) and endpoint (api-m5g7)
   - Output: HTTP error response sent to frontend API contract (api-q7v1) with message indicating that a session is already active
   - Error: If error transformation fails, return generic internal error from backend_error_definitions (db-l1c3)

## Terminal Condition

User receives an error response indicating that a session is already active and no new session is created

## Feedback Loops

None — strictly linear.
