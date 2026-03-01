# PATH: orient-state-creates-single-story-record

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

ORIENT state runs with multiple possible experiences available

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `mq-r4z8` | backend_process_chain | Executes the ORIENT state logic as an ordered backend process chain. |
| `db-f8n5` | data_structure | Defines the StoryRecord schema including story_title and initial context fields. |
| `db-j6x9` | backend_verifier | Validates required fields and structural constraints for StoryRecord before persistence. |
| `db-d3w8` | data_access_object | Handles persistence of the StoryRecord into the database. |
| `api-n8k2` | request_handler | Returns the created StoryRecord as a response to the calling layer. |
| `db-l1c3` | backend_error_definitions | Defines structured error responses for validation and persistence failures. |

## Steps

1. **Trigger ORIENT process chain**
   - Input: ORIENT state execution event with multiple candidate experiences (mq-r4z8)
   - Process: Activates the ORIENT backend process chain and passes the available experiences as input context for decision-making.
   - Output: ORIENT process chain execution context containing candidate experiences
   - Error: If ORIENT process chain is not registered or fails to start, return a system error defined in backend_error_definitions (db-l1c3) and abort execution.

2. **Select single experience and derive story data**
   - Input: ORIENT execution context with multiple possible experiences (mq-r4z8)
   - Process: Evaluates the available experiences, selects exactly one according to business rules, and derives a story_title and initial context payload from the selected experience.
   - Output: Story creation payload containing story_title and initial context
   - Error: If no valid experience can be selected, return a domain validation error from backend_error_definitions (db-l1c3) and stop further processing.

3. **Validate StoryRecord structure**
   - Input: Story creation payload with story_title and initial context (db-f8n5, db-j6x9)
   - Process: Applies backend verifier rules to ensure required fields (story_title and initial context) are present and conform to structural constraints before persistence.
   - Output: Validated StoryRecord entity ready for persistence
   - Error: If validation fails, backend_verifier (db-j6x9) raises a validation error and the process returns a structured error response without creating a record.

4. **Persist StoryRecord**
   - Input: Validated StoryRecord entity (db-d3w8)
   - Process: Uses the data access object to insert exactly one new StoryRecord into the underlying data store.
   - Output: Persisted StoryRecord with unique identifier and stored story_title and initial context
   - Error: If database insertion fails, data_access_object (db-d3w8) returns a persistence error defined in backend_error_definitions (db-l1c3) and no partial record remains.

5. **Return StoryRecord to interface**
   - Input: Persisted StoryRecord entity (api-n8k2)
   - Process: Formats and returns the created StoryRecord through the request handler to the calling layer so it can be rendered to the user.
   - Output: API response containing the created StoryRecord with story_title and initial context
   - Error: If response formatting or transmission fails, request_handler (api-n8k2) returns a structured backend error (db-l1c3) and logs the failure.

## Terminal Condition

User sees a newly created StoryRecord with a visible story_title and initialized context in the interface

## Feedback Loops

None — strictly linear.
