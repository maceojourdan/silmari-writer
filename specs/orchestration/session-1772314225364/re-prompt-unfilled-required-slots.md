# PATH: re-prompt-unfilled-required-slots

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User submits input while the system is actively prompting for missing required slots for a given question_type

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Captures user input and renders repeated required slot prompts |
| `api-q7v1` | frontend_api_contract | Defines typed contract between frontend and backend for slot submission and prompt responses |
| `api-m5g7` | endpoint | Receives slot submission requests and returns validation and prompt responses |
| `api-n8k2` | request_handler | Bridges endpoint requests to backend processor and service logic |
| `db-h2s4` | service | Coordinates validation and workflow state evaluation |
| `db-b7r2` | processor | Applies business rules for slot fulfillment and workflow progression control |
| `db-j6x9` | backend_verifier | Validates required slot fulfillment against defined rules |
| `db-f8n5` | data_structure | Defines required slot schema and constraints for question_type |
| `mq-r4z8` | backend_process_chain | Represents workflow step sequencing that must not advance when slots remain unfilled |
| `cfg-j9w2` | shared_error_definitions | Provides standardized error definitions for validation and state-guard failures |
| `cfg-q9c5` | backend_logging | Logs backend validation and state control events |
| `cfg-r3d7` | frontend_logging | Logs frontend rendering or state update issues |

## Steps

1. **Capture user slot input**
   - Input: User-provided slot values from ui-w8p2 (component) submitted via api-q7v1 (frontend_api_contract)
   - Process: Collect the latest user input and associate it with the current workflow context and question_type that still has missing required slots.
   - Output: Structured slot submission payload sent to api-m5g7 (endpoint) through api-n8k2 (request_handler)
   - Error: If submission payload is malformed, return validation error defined in cfg-j9w2 (shared_error_definitions) and re-render the prompt without progressing.

2. **Validate required slot fulfillment**
   - Input: Structured slot submission payload handled by api-n8k2 (request_handler) and forwarded to db-h2s4 (service)
   - Process: Evaluate whether the submitted input fills any of the currently missing required slots for the active question_type using db-j6x9 (backend_verifier) against db-f8n5 (data_structure).
   - Output: Validation result indicating which required slots remain unfilled and confirmation that no new required slots were satisfied.
   - Error: If validation logic fails or required slot definitions are inconsistent, return a domain error from cfg-j9w2 (shared_error_definitions) and log via cfg-q9c5 (backend_logging) without advancing workflow state.

3. **Enforce no workflow progression**
   - Input: Validation result showing zero newly satisfied required slots, processed within db-b7r2 (processor)
   - Process: Determine that workflow progression criteria are not met and explicitly prevent transition to the next process step in mq-r4z8 (backend_process_chain).
   - Output: Workflow state remains at current step with unchanged list of missing required slots.
   - Error: If workflow state mutation is attempted despite unmet criteria, abort transition and emit a guarded state error from cfg-j9w2 (shared_error_definitions).

4. **Generate targeted re-prompt**
   - Input: Current workflow state and list of still-missing required slots from db-b7r2 (processor)
   - Process: Construct a response that explicitly re-prompts only for the specific missing required slots, preserving prior context and attempt count.
   - Output: API response from api-m5g7 (endpoint) containing the same missing required slot prompts.
   - Error: If required slot list cannot be retrieved, return a recoverable error from cfg-j9w2 (shared_error_definitions) and display a generic clarification prompt without advancing.

5. **Render repeated prompt in UI**
   - Input: API response delivered through api-q7v1 (frontend_api_contract) to ui-w8p2 (component)
   - Process: Update the component state to display the same specific missing required slot prompts and optional guidance hint if retry threshold reached.
   - Output: User visibly sees the system re-prompting for the same missing required slots, with no navigation or progression to the next workflow step.
   - Error: If UI state update fails, log via cfg-r3d7 (frontend_logging) and re-render the current prompt from last known valid state without progression.

## Terminal Condition

User sees the system re-prompting for the same specific missing required slots, with no advancement to the next workflow step

## Feedback Loops

The submit-and-validate cycle repeats up to 5 consecutive times per workflow step while required slots remain unfilled; after 5 failed attempts, the system continues re-prompting but also displays a persistent guidance hint without progressing.
