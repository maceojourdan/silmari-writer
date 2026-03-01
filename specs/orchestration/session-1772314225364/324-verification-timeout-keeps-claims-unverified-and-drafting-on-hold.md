# PATH: verification-timeout-keeps-claims-unverified-and-drafting-on-hold

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

System clock reaches the configured verification timeout deadline for a pending voice or SMS verification request with no response received

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `cfg-l8y1` | shared_settings | Provides configured verification timeout duration |
| `db-f8n5` | data_structure | Stores verification requests, claims, and drafting workflow states |
| `db-d3w8` | data_access_object | Persists verification, claim, and drafting state updates |
| `db-h2s4` | service | Applies business rules to enforce unverified and on-hold states |
| `db-j6x9` | backend_verifier | Validates business rule conditions for claim and drafting states |
| `db-l1c3` | backend_error_definitions | Defines standardized backend error types for persistence and domain failures |
| `api-m5g7` | endpoint | Exposes claim and drafting status to frontend |
| `api-n8k2` | request_handler | Bridges endpoint to backend service logic |
| `ui-y5t3` | data_loader | Fetches updated claim and drafting status for UI |
| `ui-v3n6` | module | Contains drafting workflow UI state and navigation |
| `ui-w8p2` | component | Renders claim verification and drafting status to user |
| `cfg-q9c5` | backend_logging | Logs backend timeout and processing events |
| `cfg-r3d7` | frontend_logging | Logs frontend rendering or data loading errors |

## Steps

1. **Detect verification timeout event**
   - Input: Scheduled job trigger and verification timeout duration from cfg-l8y1 (shared_settings); pending verification records from db-f8n5 (data_structure)
   - Process: Identify verification requests sent via voice or SMS that have exceeded the configured timeout duration without receiving a response.
   - Output: List of verification records marked as expired due to timeout.
   - Error: If shared_settings cannot be loaded, log configuration error via cfg-q9c5 and skip evaluation for this cycle; if data access fails, raise persistence error defined in db-l1c3.

2. **Update verification status to timed-out**
   - Input: Expired verification records; db-d3w8 (data_access_object); db-f8n5 (data_structure)
   - Process: Persist status change for each expired verification request to a terminal "Timed Out" state while ensuring no response has been recorded.
   - Output: Verification records stored with status "Timed Out" and no associated response.
   - Error: If record was already responded to concurrently, abort update for that record and log concurrency conflict via db-l1c3; if persistence fails, return data access error.

3. **Enforce claims remain unverified and drafting on hold**
   - Input: Timed-out verification records; related claim and drafting entities from db-f8n5 (data_structure); db-h2s4 (service)
   - Process: Ensure associated claims retain or revert to "Unverified" status and confirm the drafting workflow state remains "On Hold" when verification is timed out.
   - Output: Claim entities explicitly marked "Unverified" and drafting workflow state confirmed as "On Hold".
   - Error: If claim or drafting entity is missing, log domain integrity error via db-l1c3; if business rule validation fails, surface validation failure via db-j6x9.

4. **Expose updated status to frontend**
   - Input: Updated claim and drafting states from db-f8n5 (data_structure); api-m5g7 (endpoint); api-n8k2 (request_handler); ui-y5t3 (data_loader)
   - Process: Serve the current claim verification and drafting status through the backend endpoint so the frontend can retrieve and reflect the updated state.
   - Output: API response containing claim status "Unverified" and drafting status "On Hold".
   - Error: If endpoint processing fails, return standardized error from db-l1c3; if request handling fails, log via cfg-q9c5 and return error response.

5. **Render timeout state in drafting UI**
   - Input: API response with claim and drafting statuses; ui-v3n6 (module); ui-w8p2 (component)
   - Process: Update the drafting interface to display the claim as "Unverified" and show the drafting process as "On Hold" with a visible indication that verification has timed out.
   - Output: User-visible drafting screen showing "Unverified" claims and "On Hold" drafting status due to verification timeout.
   - Error: If data loading fails, show error state in component and log via cfg-r3d7; if status values are missing, display fallback "Status Unavailable" indicator.

## Terminal Condition

User sees in the drafting interface that the claims are marked as "Unverified" and the drafting process status remains "On Hold" with an indication that verification timed out

## Feedback Loops

None — strictly linear.
