# PATH: confirm-aligned-story-selection

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User is presented with a question and related job requirements, selects one story that aligns with both, and clicks the confirm button.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `db-f8n5` | data_structure | Stores question, job requirements, and story entities with status fields. |
| `db-d3w8` | data_access_object | Persists story confirmation status updates. |
| `db-h2s4` | service | Coordinates validation and persistence for story confirmation. |
| `db-j6x9` | backend_verifier | Validates story alignment with active question and job requirements. |
| `db-l1c3` | backend_error_definitions | Defines domain and persistence errors returned to the client. |
| `api-m5g7` | endpoint | Receives confirmation requests and returns responses. |
| `api-q7v1` | frontend_api_contract | Typed contract used by frontend to call confirmation endpoint. |
| `ui-v3n6` | module | Frontend module managing story selection and next step navigation. |
| `ui-w8p2` | component | UI component for selecting and confirming a story. |
| `ui-y5t3` | data_loader | Fetches question, job requirements, and stories for display. |
| `ui-a4y1` | frontend_verifier | Prevents submission when no story is selected. |

## Steps

1. **Render question requirements and stories**
   - Input: Active question and related job requirements context from db-f8n5 (data_structure), list of available stories from db-f8n5 (data_structure), delivered via api-m5g7 (endpoint) and consumed by ui-y5t3 (data_loader) in ui-v3n6 (module).
   - Process: Retrieve and present the current question, its related job requirements, and the list of available stories to the user in a single selection interface.
   - Output: UI displays the question, job requirements, and selectable list of stories.
   - Error: If question, job requirements, or stories cannot be retrieved, api-m5g7 returns a backend_error_definitions (db-l1c3) error and the UI displays an error state with retry option.

2. **Submit selected story confirmation**
   - Input: User-selected story identifier from ui-w8p2 (component) within ui-v3n6 (module), validated by ui-a4y1 (frontend_verifier), sent through api-q7v1 (frontend_api_contract) to api-m5g7 (endpoint).
   - Process: Capture the selected story ID when the user clicks confirm and send a confirmation request referencing the active question context to the backend.
   - Output: Confirmation request containing question context and selected story ID is received by the backend endpoint.
   - Error: If no story is selected, ui-a4y1 prevents submission and displays validation feedback; if the request fails in transit, api-m5g7 returns a db-l1c3 error and the UI displays a submission failure message.

3. **Validate story alignment and eligibility**
   - Input: Confirmation request with selected story ID and active question ID from api-m5g7 (endpoint), relevant story, question, and job requirement records from db-f8n5 (data_structure).
   - Process: Use db-j6x9 (backend_verifier) to validate that the selected story exists, is associated with the active question, and satisfies the related job requirements context before confirmation is allowed.
   - Output: Validation result indicating the story is eligible for confirmation under the current question and job requirements.
   - Error: If the story does not exist, is already confirmed, or does not align with the current question and related job requirements, db-j6x9 raises a domain error mapped to backend_error_definitions (db-l1c3), and api-m5g7 returns a structured error response to the UI.

4. **Mark story as confirmed and restrict scope**
   - Input: Validated confirmation request and story record from db-f8n5 (data_structure), coordinated by db-h2s4 (service) and persisted via db-d3w8 (data_access_object).
   - Process: Update the selected story status to confirmed for the active question and mark all other available stories for that question as excluded from the next step context.
   - Output: Persisted state where exactly one story is marked confirmed for the question and others are not considered for subsequent processing.
   - Error: If persistence fails, db-d3w8 returns a db-l1c3 persistence error and the service aborts the operation without partial updates.

5. **Display confirmed story for next step**
   - Input: Successful confirmation response from api-m5g7 (endpoint) containing the confirmed story details.
   - Process: Update the UI state in ui-v3n6 (module) to mark the selected story as confirmed and navigate to the next step screen showing only that single confirmed story.
   - Output: User sees the selected story marked as confirmed and the next step interface limited to that single story.
   - Error: If the response cannot be processed, the UI shows a db-l1c3-based error message and remains on the selection screen without advancing.

## Terminal Condition

User sees the selected story marked as confirmed in the interface and the next step screen displays only that single confirmed story.

## Feedback Loops

None — strictly linear.
