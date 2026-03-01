# PATH: prevent-edit-of-locked-answer

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User attempts to edit and submit changes to an answer that has already been finalized and locked

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Captures user edit attempt and displays locked error message |
| `ui-a4y1` | frontend_verifier | Validates client-side edit submission before API call |
| `api-q7v1` | frontend_api_contract | Defines typed contract for update answer API call |
| `api-m5g7` | endpoint | Receives HTTP update request for answer edits |
| `api-n8k2` | request_handler | Bridges endpoint to backend service layer |
| `db-h2s4` | service | Orchestrates business logic including lock status verification |
| `db-d3w8` | data_access_object | Retrieves and persists answer data from the database |
| `db-f8n5` | data_structure | Represents the answer entity including finalized/locked status field |
| `db-l1c3` | backend_error_definitions | Defines structured error codes and messages for locked answer and related failures |

## Steps

1. **User submits edit request**
   - Input: User interaction in ui-w8p2 (component) containing updated answer content and answer identifier
   - Process: The frontend component captures the edit action and prepares an API request to update the answer.
   - Output: Structured update request sent through api-q7v1 (frontend_api_contract) to the backend endpoint
   - Error: If required fields are missing on the client, ui-a4y1 (frontend_verifier) blocks submission and displays validation errors.

2. **Endpoint receives update request**
   - Input: HTTP update request handled by api-m5g7 (endpoint) and routed via api-n8k2 (request_handler)
   - Process: The endpoint validates request structure and forwards the update command to the backend service layer.
   - Output: Service-level update command containing answer ID and proposed changes
   - Error: Malformed or unauthorized requests are rejected with appropriate error from db-l1c3 (backend_error_definitions) and returned to client.

3. **Service checks lock status**
   - Input: Update command received by db-h2s4 (service) with answer ID; answer data retrieved via db-d3w8 (data_access_object) from db-f8n5 (data_structure)
   - Process: The service retrieves the current answer record and verifies whether it is marked as finalized and locked.
   - Output: Determination that the answer is locked, preventing modification
   - Error: If the answer does not exist, a not-found error from db-l1c3 (backend_error_definitions) is returned; if data retrieval fails, a persistence error from db-l1c3 is returned.

4. **Reject update due to locked status**
   - Input: Locked status confirmation from db-h2s4 (service)
   - Process: The service aborts the update operation and generates a domain error indicating that the answer is locked and cannot be modified.
   - Output: Error response with locked-answer error code defined in db-l1c3 (backend_error_definitions)
   - Error: [PROPOSED: LOCKED_ANSWER_MODIFICATION_FORBIDDEN error definition in backend_error_definitions] if a specific locked-answer error type does not yet exist.

5. **Frontend displays locked message**
   - Input: Error response received via api-q7v1 (frontend_api_contract) in ui-w8p2 (component)
   - Process: The frontend component interprets the locked-answer error code and displays a user-visible notification indicating that the answer is locked and cannot be edited.
   - Output: Visible error message shown to the user and no changes reflected in the answer content
   - Error: If the error code is unrecognized, a generic error message is displayed while preserving the original answer state.

## Terminal Condition

User sees a clear error message in the UI stating that the answer is locked and no changes are applied

## Feedback Loops

None — strictly linear.
