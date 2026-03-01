# PATH: finalize-answer-locks-editing

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User clicks the "Finalize" action on an editable completed answer

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Captures the Finalize action and updates UI state to disable editing |
| `ui-v3n6` | module | Contains the answer editing and finalization workflow |
| `api-q7v1` | frontend_api_contract | Defines typed contract for finalize answer API call |
| `api-m5g7` | endpoint | Exposes backend HTTP route for finalizing an answer |
| `api-n8k2` | request_handler | Bridges endpoint to processor logic |
| `db-b7r2` | processor | Coordinates finalize operation execution |
| `db-h2s4` | service | Implements business logic to validate and lock the answer |
| `db-d3w8` | data_access_object | Handles persistence and update of answer record |
| `db-f8n5` | data_structure | Defines answer entity schema including finalized and editable fields |
| `db-j6x9` | backend_verifier | Validates that answer is completed and eligible for finalization |
| `db-l1c3` | backend_error_definitions | Defines backend error types for invalid finalize attempts |
| `cfg-j9w2` | shared_error_definitions | Defines cross-layer error messages displayed to the user |

## Steps

1. **Capture Finalize Action**
   - Input: User interaction event in ui-w8p2 (component) within ui-v3n6 (module)
   - Process: The component detects the "Finalize" action, verifies the answer is currently editable in local state, and prepares a finalize request with the answer identifier.
   - Output: Structured finalize request sent via api-q7v1 (frontend_api_contract)
   - Error: If the answer is already marked as finalized in local state, the action is blocked and a user-visible message is shown using cfg-j9w2 (shared_error_definitions).

2. **Handle Finalize API Request**
   - Input: HTTP finalize request received at api-m5g7 (endpoint)
   - Process: The endpoint forwards the request to api-n8k2 (request_handler), which invokes db-b7r2 (processor) to execute the finalize operation for the specified answer.
   - Output: Invocation of backend service layer with answer identifier and user context
   - Error: If authentication or request validation fails, the endpoint returns an appropriate error defined in db-l1c3 (backend_error_definitions).

3. **Validate and Lock Answer**
   - Input: Answer identifier and user context in db-h2s4 (service), accessing db-d3w8 (data_access_object) and db-f8n5 (data_structure)
   - Process: The service retrieves the answer entity, verifies via db-j6x9 (backend_verifier) that it is completed and not already finalized, then updates its status to finalized and sets it as non-editable.
   - Output: Persisted answer record with finalized status and editability disabled
   - Error: If the answer is not found, not completed, or already finalized, the service returns a domain error from db-l1c3 (backend_error_definitions) and no state change is persisted.

4. **Return Finalized State to Frontend**
   - Input: Updated answer entity from db-h2s4 (service)
   - Process: The processor returns the updated finalized answer through api-n8k2 (request_handler) and api-m5g7 (endpoint) as a success response.
   - Output: HTTP success response containing finalized answer state
   - Error: If response serialization fails, a standardized error from db-l1c3 (backend_error_definitions) is returned.

5. **Update UI to Locked State**
   - Input: Finalize success response via api-q7v1 (frontend_api_contract) into ui-w8p2 (component)
   - Process: The component updates its local state to reflect the finalized status and disables or removes all editing controls for the answer.
   - Output: User interface shows answer as finalized with editing disabled
   - Error: If the response indicates failure, the component displays a user-visible error message using cfg-j9w2 (shared_error_definitions) and keeps the answer editable.

## Terminal Condition

User sees the answer marked as finalized and all editing controls are disabled or removed, preventing further edits

## Feedback Loops

None — strictly linear.
