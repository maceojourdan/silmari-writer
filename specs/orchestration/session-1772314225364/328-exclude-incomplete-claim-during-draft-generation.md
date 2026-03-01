# PATH: exclude-incomplete-claim-during-draft-generation

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User initiates the draft generation process for a set of Confirmed claims

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `api-m5g7` | endpoint | Exposes the draft generation HTTP route |
| `api-n8k2` | request_handler | Bridges the HTTP request to backend processing logic |
| `api-q7v1` | frontend_api_contract | Defines the typed contract used by the frontend to call draft generation and receive omission notices |
| `db-d3w8` | data_access_object | Retrieves Confirmed claim entities from persistence |
| `db-f8n5` | data_structure | Represents claim entities including structural metadata fields |
| `db-j6x9` | backend_verifier | Validates required structural metadata completeness for claims |
| `db-h2s4` | service | Orchestrates draft generation workflow and exclusion logic |
| `db-b7r2` | processor | Executes core draft assembly logic |
| `db-l1c3` | backend_error_definitions | Defines standardized backend errors for request, validation, and processing failures |
| `cfg-q9c5` | backend_logging | Logs validation and processing failures during draft generation |

## Steps

1. **Receive draft generation request**
   - Input: Draft generation HTTP request received by api-m5g7 and routed through api-n8k2
   - Process: Accept and normalize the draft generation request, identifying the target set of Confirmed claims to be included in the draft
   - Output: Structured draft generation command containing claim selection criteria
   - Error: If request payload is invalid or missing required parameters, return standardized error defined in db-l1c3 and do not proceed

2. **Retrieve Confirmed claims**
   - Input: Draft generation command and db-d3w8 for accessing claim data structures db-f8n5
   - Process: Query the data store for all claims with status Confirmed that match the selection criteria
   - Output: Collection of Confirmed claim entities
   - Error: If data access fails, raise data access error via db-l1c3 and abort draft generation

3. **Validate structural metadata completeness**
   - Input: Collection of Confirmed claim entities and validation rules from db-j6x9 applied to db-f8n5
   - Process: Evaluate each claim for presence of required structural metadata fields and partition them into complete and incomplete sets
   - Output: Two collections: structurally complete claims eligible for drafting and incomplete claims marked with missing metadata details
   - Error: If validation rules cannot be evaluated, log validation failure via cfg-q9c5 and treat affected claims as incomplete to prevent unsafe inclusion

4. **Assemble draft from complete claims**
   - Input: Structurally complete claims and draft orchestration via db-h2s4 and db-b7r2
   - Process: Generate draft content using only the structurally complete claims, explicitly excluding any claims flagged as incomplete
   - Output: Draft document content and internal omission report listing excluded claim identifiers and reasons
   - Error: If draft assembly fails, return processing error defined in db-l1c3 and do not persist partial draft

5. **Return draft and omission notice**
   - Input: Draft document content and omission report routed through api-n8k2 to api-m5g7 and exposed via api-q7v1
   - Process: Send response containing the generated draft and a user-visible notice that specific claims were omitted due to missing required structural metadata
   - Output: HTTP response with draft content and explicit omission message displayed in the frontend
   - Error: If response serialization fails, log via cfg-q9c5 and return standardized server error from db-l1c3

## Terminal Condition

User sees the generated draft containing only structurally complete Confirmed claims and a visible notice stating that one specific claim was omitted due to missing required structural metadata

## Feedback Loops

None — strictly linear.
