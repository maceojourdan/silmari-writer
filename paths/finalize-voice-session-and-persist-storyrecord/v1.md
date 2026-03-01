# PATH: finalize-voice-session-and-persist-storyrecord

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User clicks the "Finalize Session" action after completing all required voice inputs in an active session.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Provides the finalize session action and displays finalization confirmation. |
| `api-q7v1` | frontend_api_contract | Defines typed contract for finalize session API call. |
| `api-m5g7` | endpoint | Receives HTTP request to finalize session. |
| `api-n8k2` | request_handler | Bridges endpoint to backend service logic. |
| `db-h2s4` | service | Orchestrates validation, state transition to FINALIZE, and StoryRecord persistence. |
| `db-d3w8` | data_access_object | Persists session and StoryRecord entities. |
| `db-f8n5` | data_structure | Represents session and StoryRecord entities with state and response fields. |
| `db-l1c3` | backend_error_definitions | Defines domain and persistence errors for finalization flow. |
| `cfg-j9w2` | shared_error_definitions | Defines cross-layer validation and request errors. |
| `cfg-r3d7` | frontend_logging | Logs UI update errors during finalization display. |

## Steps

1. **Submit finalize session request**
   - Input: User interaction from UI component (ui-w8p2) invoking frontend API contract (api-q7v1) targeting backend endpoint (api-m5g7) with active session identifier.
   - Process: Send a finalize-session request containing the active session ID to the backend endpoint responsible for session finalization.
   - Output: HTTP request received by backend endpoint for session finalization.
   - Error: If the request is malformed or missing session ID, backend returns validation error defined in shared_error_definitions (cfg-j9w2) and user remains on session screen with error message.

2. **Validate session eligibility for finalization**
   - Input: Finalize request handled by request_handler (api-n8k2) and passed to backend service (db-h2s4) with session ID.
   - Process: Verify that the session exists, is active, and has all required voice inputs completed before allowing finalization.
   - Output: Validated active session eligible for finalization.
   - Error: If session does not exist, is not active, or required inputs are incomplete, service returns domain error from backend_error_definitions (db-l1c3) and no state changes occur.

3. **Update session state to FINALIZE**
   - Input: Validated session entity from data_structure (db-f8n5) accessed via data_access_object (db-d3w8).
   - Process: Change the session state field to the explicit value FINALIZE and persist the updated session entity.
   - Output: Session record stored with state set to FINALIZE.
   - Error: If persistence fails, data_access_object (db-d3w8) returns persistence error from backend_error_definitions (db-l1c3) and the transaction is aborted with no partial updates.

4. **Persist StoryRecord with FINALIZED status and responses**
   - Input: Session in FINALIZE state and collected voice responses from data_structure (db-f8n5) via data_access_object (db-d3w8).
   - Process: Create or update the associated StoryRecord entity, set its status to FINALIZED, and store all collected responses as part of the persisted record.
   - Output: StoryRecord persisted with status FINALIZED and all collected responses saved.
   - Error: If StoryRecord persistence fails, backend_error_definitions (db-l1c3) error is returned and session state change is rolled back to prevent inconsistency.

5. **Return confirmation response to user**
   - Input: Successful session update and StoryRecord persistence from backend service (db-h2s4).
   - Process: Construct and send a success response indicating session state FINALIZE and StoryRecord status FINALIZED.
   - Output: Frontend receives confirmation payload with session state FINALIZE and StoryRecord status FINALIZED.
   - Error: If response construction fails, backend_error_definitions (db-l1c3) error is logged and a generic failure response is returned.

6. **Display finalized session state in UI**
   - Input: Success response consumed by UI component (ui-w8p2).
   - Process: Update the UI state to reflect that the session state is FINALIZE and the StoryRecord status is FINALIZED, and display a visible confirmation to the user.
   - Output: User sees confirmation that the session state is FINALIZE and the StoryRecord is persisted with status FINALIZED and all collected responses saved.
   - Error: If UI state update fails, frontend_logging (cfg-r3d7) logs the error and user is shown a retry prompt without altering backend state.

## Terminal Condition

User sees confirmation that the session state is now FINALIZE and the StoryRecord is persisted with status FINALIZED, with all collected responses saved and reflected in the session view.

## Feedback Loops

None — strictly linear.
