# PATH: confirm-metric-claim-truth-check

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User selects Y (confirm) or N (deny) on a displayed extracted metric claim and submits the decision.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Captures user confirmation decision and updates UI state. |
| `ui-a4y1` | frontend_verifier | Validates that user has selected Y or N before submission. |
| `api-q7v1` | frontend_api_contract | Defines typed request from frontend to backend for truth check confirmation. |
| `api-m5g7` | endpoint | Receives HTTP confirmation request for truth check. |
| `api-n8k2` | request_handler | Bridges endpoint request to backend service logic. |
| `db-h2s4` | service | Orchestrates business logic for storing truth check entry. |
| `db-d3w8` | data_access_object | Persists truth_checks entry to database. |
| `db-f8n5` | data_structure | Defines schema for truth_checks table/entity including status and source fields. |
| `db-l1c3` | backend_error_definitions | Defines structured backend errors for validation and persistence failures. |

## Steps

1. **Submit confirmation decision**
   - Input: User decision (Y/N), metric claim identifier, and source displayed in frontend component (ui-w8p2).
   - Process: Frontend component captures the user's selection and prepares a structured confirmation payload containing claim ID, selected status (confirmed/denied), and source.
   - Output: Structured confirmation request ready to be sent via frontend API contract (api-q7v1).
   - Error: If no selection is made, frontend validation blocks submission using frontend_verifier (ui-a4y1) and displays inline validation error.

2. **Send confirmation request**
   - Input: Structured confirmation payload from frontend component via frontend API contract (api-q7v1).
   - Process: Frontend API contract sends HTTP request to backend endpoint (api-m5g7) responsible for truth check confirmations.
   - Output: HTTP request containing claim_id, status (confirmed/denied), and source delivered to backend endpoint.
   - Error: If network request fails, frontend displays error notification and allows up to 2 retries before final failure message.

3. **Handle confirmation request**
   - Input: HTTP request received by backend endpoint (api-m5g7).
   - Process: Endpoint delegates request to request handler (api-n8k2), which validates required fields and forwards a normalized command to backend service (db-h2s4).
   - Output: Validated truth check confirmation command passed to service layer.
   - Error: If required fields are missing or invalid, backend returns structured error using backend_error_definitions (db-l1c3) and responds with client-visible error.

4. **Persist truth check entry**
   - Input: Validated confirmation command (claim_id, status, source) received by backend service (db-h2s4).
   - Process: Service orchestrates data access object (db-d3w8) to create and store a new truth_checks record in the corresponding data structure (db-f8n5) with status set to confirmed or denied and associated source.
   - Output: Persisted truth_checks record with stored status and source.
   - Error: If database write fails, DAO returns persistence error defined in backend_error_definitions (db-l1c3); service propagates error response to endpoint.

5. **Return updated status to frontend**
   - Input: Successful persistence result from service layer.
   - Process: Backend endpoint (api-m5g7) returns success response containing stored status and source; frontend component (ui-w8p2) updates local state to reflect confirmed/denied status.
   - Output: UI displays the metric claim as Confirmed or Denied with persisted state reflected.
   - Error: If response parsing fails on frontend, error is logged and user is shown a generic failure message with option to refresh.

## Terminal Condition

User sees the metric claim marked as Confirmed or Denied in the UI, and the truth_checks entry is persisted with the selected status and source.

## Feedback Loops

If persistence fails, the system allows the user to retry submission up to 2 additional times before displaying a final error state.
