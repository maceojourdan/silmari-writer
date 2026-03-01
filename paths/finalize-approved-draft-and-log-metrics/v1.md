# PATH: finalize-approved-draft-and-log-metrics

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User executes FINALIZE action on an approved draft

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `api-q7v1` | frontend_api_contract | Defines the FINALIZE request contract between frontend and backend |
| `api-n8k2` | request_handler | Bridges FINALIZE endpoint to backend processor logic |
| `db-b7r2` | processor | Executes finalization logic and coordinates export and metrics computation |
| `db-d3w8` | data_access_object | Retrieves and persists draft and metrics data |
| `db-f8n5` | data_structure | Represents draft entity including status, timestamps, and interaction data |
| `db-l1c3` | backend_error_definitions | Defines error types for invalid state, persistence failure, or processing errors |
| `cfg-p4b8` | shared_logging | Logs computed metrics and cross-layer events |
| `cfg-q9c5` | backend_logging | Logs backend processing and error events during finalization |

## Steps

1. **Invoke Finalize Endpoint**
   - Input: User action FINALIZE with approved draft identifier via frontend API contract (api-q7v1)
   - Process: Frontend sends a FINALIZE request to the backend endpoint, including draft ID and user context.
   - Output: HTTP request delivered to backend endpoint for FINALIZE operation
   - Error: If request is malformed or network fails, endpoint returns standardized error from shared_error_definitions (cfg-j9w2) and user sees failure notification.

2. **Validate Draft Approval State**
   - Input: FINALIZE request handled by request handler (api-n8k2) and delegated to processor (db-b7r2) with draft entity from data_structure (db-f8n5) via DAO (db-d3w8)
   - Process: System retrieves the draft and verifies it is in APPROVED state and eligible for finalization.
   - Output: Validated approved draft ready for finalization
   - Error: If draft not found or not in APPROVED state, backend_error_definitions (db-l1c3) error is returned and surfaced to user; no export or metrics logging occurs.

3. **Generate Exportable Answer Artifact**
   - Input: Approved draft content and metadata from data_structure (db-f8n5)
   - Process: Processor transforms the approved draft into an exportable answer format and marks it as finalized.
   - Output: Exportable answer artifact and updated draft status = FINALIZED persisted via DAO (db-d3w8)
   - Error: If transformation or persistence fails, backend_error_definitions (db-l1c3) error is logged via backend_logging (cfg-q9c5) and returned to user; draft remains in APPROVED state.

4. **Compute and Log Metrics**
   - Input: Finalized draft timestamps and interaction data from data_structure (db-f8n5)
   - Process: System calculates time-to-draft, confirmation rate, and signal density, then records these metrics using shared_logging (cfg-p4b8) and/or persistence via DAO (db-d3w8).
   - Output: Metrics log entries associated with finalized draft
   - Error: If metrics computation or logging fails, error is recorded via shared_logging (cfg-p4b8); FINALIZED state and export remain valid but error is flagged for monitoring.

5. **Return Export Response to User**
   - Input: Exportable answer artifact and successful FINALIZED status from processor (db-b7r2)
   - Process: Request handler (api-n8k2) constructs success response including export payload or download link and confirmation of metrics logging.
   - Output: User receives downloadable/exportable answer and visible confirmation of successful finalization
   - Error: If response construction fails, backend_error_definitions (db-l1c3) error is returned and logged; user is informed that finalization may require retry.

## Terminal Condition

User receives an exportable answer file/download and sees confirmation that metrics were recorded for the finalized draft

## Feedback Loops

None — strictly linear.
