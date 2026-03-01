# PATH: draft-state-filters-unconfirmed-hard-claims-and-records-claims-used

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

StoryRecord with truth_checks enters or executes the DRAFT state in the backend process chain

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `db-f8n5` | data_structure | Defines StoryRecord schema including truth_checks, draft_text, and claims_used fields. |
| `db-d3w8` | data_access_object | Handles retrieval and persistence of StoryRecord entities. |
| `db-h2s4` | service | Encapsulates drafting business logic and orchestration. |
| `db-j6x9` | backend_verifier | Validates truth_check structure and claim eligibility rules. |
| `db-l1c3` | backend_error_definitions | Provides structured error types for drafting, validation, and persistence failures. |
| `mq-r4z8` | backend_process_chain | Triggers and sequences DRAFT state execution. |
| `api-n8k2` | request_handler | Delivers updated draft response to the caller for user display. |

## Steps

1. **Trigger DRAFT execution**
   - Input: StoryRecord containing truth_checks from db-f8n5 (data_structure), invoked via mq-r4z8 (backend_process_chain)
   - Process: Detect that the StoryRecord is in DRAFT state and initiate the drafting operation for that record.
   - Output: DRAFT execution context containing StoryRecord data and associated truth_checks
   - Error: If StoryRecord is missing or not in DRAFT state, raise a domain error defined in db-l1c3 (backend_error_definitions) and halt execution.

2. **Load full StoryRecord with truth checks**
   - Input: StoryRecord identifier from DRAFT execution context; db-d3w8 (data_access_object)
   - Process: Retrieve the persisted StoryRecord including all truth_checks and claim attributes required for drafting.
   - Output: Complete StoryRecord entity with structured truth_checks
   - Error: If retrieval fails or truth_checks are malformed, raise a data access or validation error via db-l1c3 (backend_error_definitions).

3. **Filter unconfirmed hard claims**
   - Input: StoryRecord with truth_checks from db-f8n5 (data_structure)
   - Process: Evaluate each hard claim against its truth_check status and exclude any hard claims that are not confirmed from the draftable content set.
   - Output: Filtered claim set containing only confirmed hard claims and other allowed content elements
   - Error: If a claim lacks required confirmation metadata, treat it as unconfirmed and exclude it; if truth_check structure violates validation rules, raise validation error via db-j6x9 (backend_verifier).

4. **Generate draft text and claims_used metadata**
   - Input: Filtered claim set and StoryRecord context; db-h2s4 (service)
   - Process: Compose draft_text using only the filtered claims and generate claims_used metadata listing identifiers of claims included in the draft.
   - Output: Draft payload containing draft_text and claims_used metadata
   - Error: If draft generation fails, raise a service-level error defined in db-l1c3 (backend_error_definitions) and abort persistence.

5. **Persist draft and metadata**
   - Input: Draft payload with draft_text and claims_used; db-d3w8 (data_access_object)
   - Process: Update the StoryRecord in storage to save the generated draft_text and associated claims_used metadata.
   - Output: Persisted StoryRecord reflecting updated draft_text and claims_used fields
   - Error: If persistence fails, raise a data access error via db-l1c3 (backend_error_definitions) and ensure no partial update is committed.

6. **Return updated draft to caller**
   - Input: Persisted StoryRecord with draft_text and claims_used; api-n8k2 (request_handler) or mq-r4z8 (backend_process_chain)
   - Process: Return the updated StoryRecord or draft view model to the initiating caller so it can be displayed.
   - Output: Response payload containing draft_text without unconfirmed hard claims and visible claims_used metadata
   - Error: If response transformation fails, raise an API or processing error via db-l1c3 (backend_error_definitions).

## Terminal Condition

User sees generated draft text that excludes unconfirmed hard claims and can view claims_used metadata associated with the draft

## Feedback Loops

None — strictly linear.
