# PATH: handle-disputed-claims-and-block-drafting

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

Claimant replies to the SMS verification request indicating that one or more key claims are incorrect.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `api-m5g7` | endpoint | Receives SMS webhook dispute response. |
| `api-n8k2` | request_handler | Transforms webhook request into service invocation. |
| `db-h2s4` | service | Orchestrates claim status updates and drafting state transitions. |
| `db-d3w8` | data_access_object | Persists claim and case state updates to the database. |
| `db-f8n5` | data_structure | Represents claim and case entities with verification and drafting status fields. |
| `db-j6x9` | backend_verifier | Validates allowed state transitions for claims and drafting process. |
| `db-l1c3` | backend_error_definitions | Defines standardized backend error responses. |
| `api-q7v1` | frontend_api_contract | Provides typed contract for fetching updated claim and case state. |
| `ui-y5t3` | data_loader | Loads case and claim status data into frontend state. |
| `cfg-r3d7` | frontend_logging | Logs frontend errors related to blocked drafting state. |

## Steps

1. **Receive SMS dispute response**
   - Input: Incoming HTTP request from SMS provider webhook containing claimant identifier and dispute details via api-m5g7 (endpoint).
   - Process: Accept and validate the webhook request, ensuring it corresponds to an existing verification request and extracting the disputed claim identifiers.
   - Output: Structured dispute response data passed to request handler.
   - Error: If the request is malformed or does not match an active verification request, return an error response defined in db-l1c3 and log the incident.

2. **Invoke dispute handling service**
   - Input: Structured dispute response data from api-n8k2 (request_handler).
   - Process: Delegate the dispute event to the backend service responsible for claim verification state management.
   - Output: Service invocation with claimant ID and disputed claim IDs.
   - Error: If handler-to-service mapping fails, return a standardized backend error from db-l1c3.

3. **Mark disputed claims as not verified**
   - Input: Claimant ID and disputed claim IDs within db-h2s4 (service).
   - Process: Update each referenced claim in the underlying data store to set verification status to 'not_verified' and record dispute metadata.
   - Output: Persisted claim records with updated verification status in db-f8n5 via db-d3w8.
   - Error: If any claim record cannot be found or updated, raise a persistence error from db-l1c3 and abort further state transitions.

4. **Block drafting process**
   - Input: Updated claim verification statuses from db-f8n5.
   - Process: Evaluate the overall case state and set the drafting status to 'blocked_due_to_unverified_claims' if one or more claims are not verified.
   - Output: Persisted case state reflecting drafting blocked status.
   - Error: If state transition rules are violated, trigger validation failure via db-j6x9 and return error defined in db-l1c3.

5. **Enforce drafting access restriction in UI**
   - Input: Frontend request to access drafting module evaluated against current case state via ui-y5t3 (data_loader).
   - Process: Fetch latest case and claim verification status from backend API (api-q7v1) and apply access control logic to prevent drafting when status is blocked.
   - Output: UI renders drafting interface in blocked state with visible message requiring corrections and re-verification.
   - Error: If data loading fails, display an error state to the user and log via cfg-r3d7; if access control configuration is missing, mark as [PROPOSED: DraftingBlockedAccessControl guard].

## Terminal Condition

User sees the drafting interface blocked with a visible status indicating disputed claims are not verified and must be corrected before drafting can continue.

## Feedback Loops

None — strictly linear.
