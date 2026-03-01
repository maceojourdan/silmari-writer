# PATH: prevent-draft-generation-without-confirmed-claims

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User clicks the "Generate Draft" button in the draft creation UI when no claims have been marked as confirmed.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Captures user interaction and displays the no-confirmed-claims message. |
| `ui-v3n6` | module | Encapsulates the draft generation UI and state management. |
| `ui-a4y1` | frontend_verifier | Validates frontend preconditions before sending the draft request. |
| `api-q7v1` | frontend_api_contract | Defines and sends the draft generation request to the backend endpoint. |
| `api-m5g7` | endpoint | Receives the draft generation HTTP request. |
| `api-n8k2` | request_handler | Delegates the endpoint request to backend service logic and maps errors to responses. |
| `db-h2s4` | service | Orchestrates draft generation logic and enforces the rule requiring confirmed claims. |
| `db-d3w8` | data_access_object | Retrieves claims data from persistence storage. |
| `db-f8n5` | data_structure | Represents the claim entity with a confirmed status field. |
| `db-l1c3` | backend_error_definitions | Defines the no-confirmed-claims domain error and related backend error types. |
| `cfg-j9w2` | shared_error_definitions | Provides cross-layer error semantics for consistent user-facing messaging. |

## Steps

1. **Initiate draft generation request**
   - Input: User interaction in ui-w8p2 (component) within ui-v3n6 (module).
   - Process: The component captures the user’s click event on the "Generate Draft" button and triggers a draft generation request through the frontend API contract.
   - Output: A draft generation API request sent via api-q7v1 (frontend_api_contract).
   - Error: If the component is in an invalid UI state (e.g., missing required context), ui-a4y1 (frontend_verifier) blocks the request and displays a validation message.

2. **Receive and route draft generation request**
   - Input: HTTP request to api-m5g7 (endpoint) initiated by api-q7v1 (frontend_api_contract).
   - Process: The endpoint accepts the request and delegates handling to api-n8k2 (request_handler) for draft generation.
   - Output: Invocation of backend draft generation logic in db-h2s4 (service).
   - Error: If the request is malformed or unauthorized, api-m5g7 returns an appropriate error defined in db-l1c3 (backend_error_definitions).

3. **Check for confirmed claims**
   - Input: Draft generation request handled by db-h2s4 (service), querying db-d3w8 (data_access_object) for claims stored in db-f8n5 (data_structure).
   - Process: The service retrieves all claims associated with the current context and evaluates whether any are marked as confirmed.
   - Output: Determination that zero confirmed claims exist.
   - Error: If data retrieval fails, db-h2s4 returns a data access error defined in db-l1c3. If no confirmed claims are found, the service raises a domain error indicating no confirmed claims available, defined in db-l1c3.

4. **Return no-confirmed-claims response**
   - Input: Domain error from db-h2s4 (service) indicating no confirmed claims.
   - Process: The request handler maps the domain error to an HTTP error response with a user-facing message stating that no confirmed claims are available.
   - Output: HTTP response sent via api-m5g7 containing the no-confirmed-claims message and no draft payload.
   - Error: If error mapping fails, a generic error from db-l1c3 is returned with a safe fallback message.

5. **Display no confirmed claims message**
   - Input: Error response received by api-q7v1 (frontend_api_contract) in ui-w8p2 (component).
   - Process: The component interprets the error response and updates its state to display a visible message indicating that no confirmed claims are available, without rendering any draft content.
   - Output: User sees a clear message that no confirmed claims are available and no draft is generated.
   - Error: If response parsing fails, a generic error notification is shown using frontend error handling conventions [PROPOSED: frontend error notification component tied to shared error definitions cfg-j9w2].

## Terminal Condition

User sees a visible message stating that no confirmed claims are available and no draft content is created or displayed.

## Feedback Loops

None — strictly linear.
