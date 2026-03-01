# PATH: approve-draft-and-transition-to-finalize

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User selects the Approve action while viewing a draft session.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Captures Approve user interaction and updates UI state. |
| `ui-v3n6` | module | Contains the draft session view and orchestrates component state. |
| `ui-a4y1` | frontend_verifier | Validates client-side preconditions such as DRAFT state. |
| `api-q7v1` | frontend_api_contract | Defines typed contract for approval endpoint invocation. |
| `api-m5g7` | endpoint | Receives approval request and returns updated session. |
| `api-n8k2` | request_handler | Bridges endpoint to backend service logic. |
| `db-h2s4` | service | Orchestrates validation, state transition, and logging. |
| `db-d3w8` | data_access_object | Persists session state change to the database. |
| `db-f8n5` | data_structure | Defines session entity schema including state field. |
| `db-l1c3` | backend_error_definitions | Defines backend-specific error types for persistence failures. |
| `cfg-j9w2` | shared_error_definitions | Provides cross-layer error definitions for invalid state transitions. |
| `cfg-q9c5` | backend_logging | Stores approval event entry in backend logs. |
| `cfg-p4b8` | shared_logging | Fallback logging mechanism if primary logging fails. |
| `cfg-r3d7` | frontend_logging | Logs client-side transport or invocation errors. |

## Steps

1. **Capture Approve Action**
   - Input: User interaction on Approve control in frontend component (ui-w8p2) within module (ui-v3n6).
   - Process: The component captures the Approve event for the currently displayed draft session and prepares a request to transition the session state.
   - Output: Structured approval request payload containing session identifier and action type.
   - Error: If the session is not in DRAFT state on the client, block submission and surface validation message using frontend_verifier (ui-a4y1).

2. **Invoke Approval Endpoint**
   - Input: Approval request payload sent via frontend API contract (api-q7v1) to backend endpoint (api-m5g7).
   - Process: The frontend API contract submits the approval request to the backend endpoint responsible for session state transitions.
   - Output: HTTP request delivered to backend with session ID and approve action.
   - Error: Network or transport failure results in user-visible error notification and no state change; error details logged via frontend_logging (cfg-r3d7).

3. **Process Approval Request**
   - Input: Incoming approval request handled by request handler (api-n8k2) and routed to backend service (db-h2s4).
   - Process: The backend service validates that the session exists and is in DRAFT state, then orchestrates the state transition to FINALIZE.
   - Output: Validated instruction to update session state to FINALIZE.
   - Error: If session is not found or not in DRAFT state, return appropriate error defined in shared_error_definitions (cfg-j9w2) and do not proceed with state change.

4. **Persist Session State Transition**
   - Input: Validated transition request to update session state, using data access object (db-d3w8) and data structure (db-f8n5).
   - Process: The data access object updates the session record in the database, changing its state from DRAFT to FINALIZE.
   - Output: Persisted session record with state set to FINALIZE.
   - Error: If database update fails, return backend error defined in backend_error_definitions (db-l1c3) and ensure no approval event is logged.

5. **Log Approval Event**
   - Input: Successful state transition result and session identifier.
   - Process: Backend records an approval event entry in backend logging (cfg-q9c5), including session ID, action type APPROVE, and timestamp.
   - Output: Approval event entry stored in backend logs for the session.
   - Error: If logging fails, record fallback error via shared_logging (cfg-p4b8) and return error response indicating approval could not be fully completed.

6. **Return Updated Session to UI**
   - Input: Updated session entity in FINALIZE state and confirmation of logged approval event.
   - Process: Backend endpoint (api-m5g7) returns a success response with updated session state; frontend component (ui-w8p2) updates its state to reflect FINALIZE and displays confirmation.
   - Output: UI displays session status as FINALIZE with approval confirmation message.
   - Error: If response handling fails on client, display generic error and prompt user to refresh; no additional state mutation occurs.

## Terminal Condition

User sees the session status updated to FINALIZE in the UI with confirmation of approval, and an approval event entry is stored in backend logs (cfg-q9c5) for the session.

## Feedback Loops

None — strictly linear.
