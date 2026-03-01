# PATH: generate-draft-from-confirmed-claims

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User clicks the 'Generate Draft' button after a set of claims has been reviewed and marked as confirmed.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Provides the 'Generate Draft' user interface and renders the resulting structured draft. |
| `ui-a4y1` | frontend_verifier | Validates client-side input before sending draft generation request. |
| `api-q7v1` | frontend_api_contract | Defines typed contract for invoking the backend draft generation endpoint. |
| `api-m5g7` | endpoint | Receives HTTP request to initiate draft generation. |
| `api-n8k2` | request_handler | Bridges endpoint to backend service responsible for draft generation. |
| `db-h2s4` | service | Orchestrates retrieval of confirmed claims and generation of structured draft. |
| `db-d3w8` | data_access_object | Handles database queries for claims and persistence of generated draft. |
| `db-f8n5` | data_structure | Defines schema for claims and draft entities, including claim status field. |
| `cfg-d2q3` | common_structure | Defines the document structure used to organize confirmed claims into a structured draft. |
| `db-l1c3` | backend_error_definitions | Provides backend-specific error types for validation and persistence failures. |
| `cfg-j9w2` | shared_error_definitions | Defines shared error codes for cross-layer validation and transformation errors. |

## Steps

1. **Initiate draft generation request**
   - Input: User action from frontend component (ui-w8p2) invoking frontend API contract (api-q7v1) for draft generation endpoint.
   - Process: The frontend component captures the current claim set context and sends a draft generation request to the backend endpoint.
   - Output: HTTP request to backend draft generation endpoint (api-m5g7).
   - Error: If request validation fails on client side, frontend_verifier (ui-a4y1) blocks submission and displays validation messages to the user.

2. **Handle draft generation endpoint request**
   - Input: HTTP request received by backend endpoint (api-m5g7) and routed through request handler (api-n8k2).
   - Process: The request handler validates required parameters and delegates the operation to the draft generation service.
   - Output: Invocation of backend service (db-h2s4) to generate draft for the specified claim set.
   - Error: If authentication/authorization fails, return error from shared_error_definitions (cfg-j9w2). If parameters are invalid, return validation error defined in backend_error_definitions (db-l1c3).

3. **Retrieve confirmed claims**
   - Input: Claim set identifier provided to backend service (db-h2s4), which uses data access object (db-d3w8) and data structure (db-f8n5).
   - Process: The service queries the data store for all claims in the set and filters to include only those marked with status 'confirmed'.
   - Output: Collection of confirmed claim entities.
   - Error: If claim set does not exist or no confirmed claims are found, raise appropriate error from backend_error_definitions (db-l1c3) and return user-facing message.

4. **Transform confirmed claims into structured draft**
   - Input: Collection of confirmed claim entities and defined document structure from shared common structure (cfg-d2q3).
   - Process: The service organizes confirmed claims into sections and ordering defined by the document structure, producing a structured draft model.
   - Output: Structured draft object containing only confirmed claims arranged per defined structure.
   - Error: If transformation rules are inconsistent or required structural elements are missing, return transformation error from shared_error_definitions (cfg-j9w2).

5. **Persist and return generated draft**
   - Input: Structured draft object passed to data access object (db-d3w8).
   - Process: The service persists the generated draft and returns the draft representation to the endpoint, which sends it back to the frontend.
   - Output: HTTP response containing the structured draft; frontend component (ui-w8p2) renders the draft view to the user.
   - Error: If persistence fails, return storage error from backend_error_definitions (db-l1c3) and display failure notification in the UI.

## Terminal Condition

User sees a newly generated structured draft in the UI that contains only confirmed claims organized according to the defined document structure.

## Feedback Loops

None — strictly linear.
