# PATH: approve-voice-session-and-persist-story-record

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User clicks 'Approve Draft' after completing a voice session with uploaded resume, job, and question.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Frontend component where user approves draft and sees confirmation. |
| `ui-a4y1` | frontend_verifier | Validates required identifiers before sending approval request. |
| `api-q7v1` | frontend_api_contract | Defines typed contract for approval endpoint. |
| `api-m5g7` | endpoint | Backend HTTP endpoint receiving approval request. |
| `api-n8k2` | request_handler | Bridges endpoint to processor logic. |
| `api-p3e6` | filter | Applies authentication and request validation filters. |
| `db-b7r2` | processor | Aggregates approved draft and related artifacts into persistence package. |
| `db-h2s4` | service | Orchestrates transactional persistence of story and related entities. |
| `db-d3w8` | data_access_object | Executes database queries and write operations. |
| `db-f8n5` | data_structure | Defines schemas for StoryRecord, truth_checks, draft_versions, and metrics. |
| `db-l1c3` | backend_error_definitions | Standardizes error responses for validation and persistence failures. |

## Steps

1. **Submit approval request**
   - Input: Approved draft identifier and session context from ui-w8p2 (component), sent via api-q7v1 (frontend_api_contract).
   - Process: The frontend component packages the approved draft ID, resume ID, job ID, question ID, and voice session ID into a structured request and sends it to the backend endpoint.
   - Output: HTTP request to backend endpoint carrying approval payload.
   - Error: If required identifiers are missing, ui-a4y1 (frontend_verifier) blocks submission and displays validation error to the user.

2. **Receive and validate approval request**
   - Input: HTTP request at api-m5g7 (endpoint), passed through api-p3e6 (filter) and handled by api-n8k2 (request_handler).
   - Process: The endpoint authenticates the request, validates required fields and session state, and transforms the payload into a processor command.
   - Output: Validated approval command forwarded to db-b7r2 (processor).
   - Error: If authentication or validation fails, db-l1c3 (backend_error_definitions) error is returned and an error response is sent to the user.

3. **Assemble persistence package**
   - Input: Validated approval command in db-b7r2 (processor), including draft content, truth check results, and session metrics.
   - Process: The processor aggregates the approved draft, associated truth_checks, draft_versions history, and computed metrics into a single persistence package representing a StoryRecord transaction.
   - Output: Structured persistence package containing StoryRecord, truth_checks, draft_versions, and metrics entities.
   - Error: If required related data (resume, job, question, session) is not found, db-l1c3 (backend_error_definitions) error is raised and propagated to the endpoint.

4. **Persist story and related entities**
   - Input: Persistence package sent to db-h2s4 (service), which coordinates db-d3w8 (data_access_object) operations on db-f8n5 (data_structure).
   - Process: The service performs a transactional write that creates or updates StoryRecord, stores truth_checks, saves draft_versions, and records metrics in their respective data structures.
   - Output: Committed database transaction confirming stored StoryRecord and related entities.
   - Error: If any database write fails, the transaction is rolled back and db-l1c3 (backend_error_definitions) error is returned to prevent partial persistence.

5. **Return success response and update UI**
   - Input: Successful persistence result from db-h2s4 (service) returned through api-n8k2 (request_handler) and api-m5g7 (endpoint).
   - Process: The backend returns a success response with the new StoryRecord ID; the frontend updates local state and navigates to the story history view showing the approved story.
   - Output: User-visible confirmation and updated story history including the newly saved story and its metadata.
   - Error: If response mapping fails on frontend, ui-w8p2 (component) displays a generic save error and prompts user to retry.

## Terminal Condition

User sees a confirmation message that the story has been saved, and the approved story appears in their story history with associated truth checks, draft versions, and metrics.

## Feedback Loops

None — strictly linear.
