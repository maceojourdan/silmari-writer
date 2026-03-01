# PATH: generate-draft-with-only-confirmed-claims

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User executes the draft generation process for a case that contains a mix of confirmed, unconfirmed, and rejected claims.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Frontend component that triggers draft generation and displays the structured draft. |
| `api-q7v1` | frontend_api_contract | Typed frontend contract used to call the backend draft generation endpoint. |
| `api-m5g7` | endpoint | Backend HTTP endpoint that receives draft generation requests. |
| `api-n8k2` | request_handler | Bridges the endpoint to backend draft generation logic. |
| `db-h2s4` | service | Backend service orchestrating claim retrieval, filtering, and draft composition. |
| `db-d3w8` | data_access_object | Retrieves claims from persistence for the specified case. |
| `db-f8n5` | data_structure | Defines the claim entity including status (confirmed, unconfirmed, rejected). |
| `db-l1c3` | backend_error_definitions | Defines structured backend errors for validation, retrieval, and generation failures. |
| `cfg-q9c5` | backend_logging | Logs backend processing and error events during draft generation. |
| `cfg-r3d7` | frontend_logging | Logs frontend errors during request handling and draft rendering. |

## Steps

1. **Initiate draft generation request**
   - Input: User action from UI component (ui-w8p2) invoking frontend API contract (api-q7v1).
   - Process: The frontend captures the current case context and sends a draft generation request to the backend endpoint.
   - Output: HTTP request to backend draft generation endpoint (api-m5g7).
   - Error: If the request cannot be formed or sent, an error is surfaced to the user via frontend logging (cfg-r3d7) and no draft is generated.

2. **Handle draft generation endpoint**
   - Input: HTTP request received by backend endpoint (api-m5g7).
   - Process: The endpoint validates request structure and delegates execution to the request handler for draft generation.
   - Output: Invocation of draft generation request handler (api-n8k2).
   - Error: If validation fails, a structured backend error (db-l1c3) is returned to the client and displayed to the user.

3. **Orchestrate draft generation**
   - Input: Draft generation command from request handler (api-n8k2).
   - Process: The handler invokes the backend service responsible for draft generation, which orchestrates claim retrieval and filtering logic.
   - Output: Call to draft generation service (db-h2s4).
   - Error: If service invocation fails, a backend error (db-l1c3) is logged via backend logging (cfg-q9c5) and propagated to the endpoint.

4. **Retrieve and filter confirmed claims**
   - Input: Draft generation request context within service (db-h2s4), accessing claim data via data access object (db-d3w8) and claim data structure (db-f8n5).
   - Process: The service retrieves all claims for the case and filters them so that only claims marked as confirmed are retained, excluding unconfirmed or rejected claims based on status fields.
   - Output: Collection of confirmed claims ready for draft composition.
   - Error: If claim retrieval fails, a data access error (db-l1c3) is returned; if no confirmed claims exist, the service proceeds with an empty confirmed set and may include a notice in the draft.

5. **Generate structured draft from confirmed claims**
   - Input: Filtered collection of confirmed claims from service (db-h2s4).
   - Process: The service composes a structured draft document that includes all confirmed claims and omits any unconfirmed or rejected claims.
   - Output: Structured draft entity ready for response.
   - Error: If draft composition fails due to invalid claim structure, a backend error (db-l1c3) is generated and returned to the client.

6. **Return and display structured draft**
   - Input: Structured draft response from backend endpoint (api-m5g7) via frontend API contract (api-q7v1).
   - Process: The frontend receives the structured draft, updates UI state in the relevant component (ui-w8p2), and renders the draft content to the user.
   - Output: Rendered structured draft visible in the UI containing only confirmed claims.
   - Error: If rendering fails, a frontend error is logged (cfg-r3d7) and a user-visible error message is shown instead of the draft.

## Terminal Condition

User sees a generated structured draft in the UI that includes all confirmed claims and excludes all unconfirmed or rejected claims.

## Feedback Loops

None — strictly linear.
