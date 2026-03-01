# PATH: transition-to-verify-when-minimum-slots-filled

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User fills or updates fields in a behavioral question form (objective, actions, obstacles, outcome, role clarity).

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Behavioral question form component capturing slot inputs and rendering status. |
| `ui-v3n6` | module | Frontend module managing question state and navigation flow. |
| `ui-a4y1` | frontend_verifier | Client-side validation enforcing minimum slot requirements. |
| `api-q7v1` | frontend_api_contract | Typed contract used by frontend to call backend state evaluation endpoint. |
| `api-m5g7` | endpoint | Backend HTTP endpoint receiving validation and transition requests. |
| `api-n8k2` | request_handler | Bridges endpoint requests to backend service logic. |
| `db-h2s4` | service | Backend service orchestrating validation and state transition logic. |
| `db-j6x9` | backend_verifier | Server-side validation of minimum slot constraints. |
| `db-f8n5` | data_structure | Behavioral question entity schema including status field and slot definitions. |
| `db-d3w8` | data_access_object | Handles persistence of question status updates. |
| `db-l1c3` | backend_error_definitions | Defines structured backend validation and persistence errors. |
| `cfg-j9w2` | shared_error_definitions | Defines cross-layer error types for network or shared failures. |
| `cfg-r3d7` | frontend_logging | Logs UI state update or rendering issues. |

## Steps

1. **Capture slot updates in UI**
   - Input: User-entered values in behavioral question form fields within ui-w8p2 and ui-v3n6.
   - Process: Update local component state with the latest values for objective, actions list, obstacles list, outcome, and role clarity whenever the user edits fields.
   - Output: Updated frontend state representing the current behavioral question draft.
   - Error: If local state update fails or fields are malformed, frontend_verifier ui-a4y1 flags the specific field and prevents further progression until corrected.

2. **Validate minimum slot requirements on frontend**
   - Input: Current behavioral question draft from ui-w8p2 and validation rules from ui-a4y1.
   - Process: Check that objective is present, at least 3 actions exist, at least 1 obstacle exists, outcome is present, and role clarity is present.
   - Output: Validation result indicating whether minimum slot requirements are satisfied.
   - Error: If validation fails, ui-a4y1 attaches field-level error messages and keeps status unchanged; no backend call is made.

3. **Submit validation request to backend**
   - Input: Validated behavioral question draft via api-q7v1 calling api-m5g7 through api-n8k2.
   - Process: Send the current draft to a backend endpoint responsible for state evaluation and transition eligibility.
   - Output: Backend evaluation request containing structured slot data.
   - Error: If network or endpoint error occurs, shared_error_definitions cfg-j9w2 is returned and displayed as a non-blocking error banner; user may retry up to 5 times.

4. **Verify minimum slots and determine state transition**
   - Input: Behavioral question data handled by db-h2s4 and validated by db-j6x9 against db-f8n5 structure rules.
   - Process: Re-validate minimum slot constraints server-side and determine that the question qualifies for transition to VERIFY state.
   - Output: Decision result indicating eligibility for VERIFY state transition.
   - Error: If server-side validation fails, db-l1c3 defines the error type and response returns validation details without changing state.

5. **Persist state transition to VERIFY**
   - Input: Eligibility decision and question entity in db-f8n5 updated through db-d3w8.
   - Process: Update the question's status field from its current draft state to VERIFY and persist the change.
   - Output: Persisted question record with status set to VERIFY.
   - Error: If persistence fails, db-l1c3 error is returned and state remains unchanged; user is informed of failure.

6. **Reflect VERIFY state in UI**
   - Input: Successful response from backend via api-n8k2 and api-q7v1 to ui-v3n6.
   - Process: Update frontend state to reflect the new VERIFY status and re-render status indicator components.
   - Output: UI displays updated status badge/stepper showing VERIFY.
   - Error: If UI state update fails, frontend_logging cfg-r3d7 logs the issue and a fallback refresh is triggered once.

## Terminal Condition

User sees the question status indicator change to VERIFY and the UI reflects the VERIFY state (e.g., badge or stepper highlights VERIFY).

## Feedback Loops

User may correct missing or invalid slots and resubmit up to 5 times per session before a cooldown message is shown.
