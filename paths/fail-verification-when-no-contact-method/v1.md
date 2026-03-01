# PATH: fail-verification-when-no-contact-method

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

System event to initiate claimant verification after key claims have been collected

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `api-m5g7` | endpoint | Receives verification initiation request |
| `api-n8k2` | request_handler | Bridges endpoint to backend service logic |
| `db-h2s4` | service | Orchestrates verification logic and drafting guard rule |
| `db-d3w8` | data_access_object | Retrieves and persists claimant and verification attempt records |
| `db-f8n5` | data_structure | Defines claimant and verification attempt schemas |
| `db-j6x9` | backend_verifier | Validates presence of required contact methods |
| `db-l1c3` | backend_error_definitions | Provides standardized error codes and messages |
| `cfg-q9c5` | backend_logging | Logs validation, persistence, and enforcement errors |
| `ui-v3n6` | module | Displays verification status and disables drafting UI |

## Steps

1. **Receive Verification Initiation Request**
   - Input: Verification initiation call received by api-m5g7 (endpoint) and forwarded by api-n8k2 (request_handler) with claimant identifier
   - Process: Accept the request to start verification for a claimant whose key claims are already stored
   - Output: Structured verification initiation request passed to backend service layer
   - Error: If request is malformed or claimant identifier is missing, return validation error defined in db-l1c3 (backend_error_definitions)

2. **Load Claimant Data**
   - Input: Claimant identifier from request; persisted claimant record accessed via db-d3w8 (data_access_object) and db-f8n5 (data_structure)
   - Process: Retrieve claimant data including collected key claims and available contact methods (voice, SMS)
   - Output: In-memory claimant profile containing key claims and contact method fields
   - Error: If claimant record is not found, raise not-found error using db-l1c3 (backend_error_definitions) and stop processing

3. **Validate Contact Method Availability**
   - Input: Claimant profile with contact method fields; validation rules from db-j6x9 (backend_verifier)
   - Process: Check whether at least one supported contact method (voice or SMS) is present and eligible for verification
   - Output: Validation result indicating no available contact methods
   - Error: If verifier execution fails due to inconsistent data, log via cfg-q9c5 (backend_logging) and return internal validation error from db-l1c3 (backend_error_definitions)

4. **Record Verification Failure**
   - Input: Validation result indicating missing contact methods; claimant record via db-d3w8 (data_access_object)
   - Process: Create or update verification attempt record with status set to Failed and reason set to missing contact method
   - Output: Persisted verification attempt marked as Failed in db-f8n5 (data_structure)
   - Error: If persistence fails, log failure via cfg-q9c5 (backend_logging) and return persistence error defined in db-l1c3 (backend_error_definitions)

5. **Prevent Drafting From Starting**
   - Input: Failed verification status from persisted record; drafting initiation logic in db-h2s4 (service)
   - Process: Enforce business rule that drafting cannot start when latest verification attempt status is Failed
   - Output: Drafting initiation request is rejected and response indicates verification failure status
   - Error: If drafting state is already in progress due to prior inconsistency, mark drafting as blocked and log corrective action via cfg-q9c5 (backend_logging) [PROPOSED: explicit DraftingStateGuard resource]

6. **Return Failure Response to Frontend**
   - Input: Rejected drafting initiation and verification failure status from service layer via api-n8k2 (request_handler)
   - Process: Send structured API response indicating verification failed due to no contact method and drafting is disabled
   - Output: Frontend receives failure response; ui-v3n6 (module) reflects verification status as Failed and disables drafting controls
   - Error: If response serialization fails, log via cfg-q9c5 (backend_logging) and return generic failure from db-l1c3 (backend_error_definitions)

## Terminal Condition

User sees that verification status is marked as Failed due to missing contact method and drafting functionality is disabled or prevented from starting

## Feedback Loops

None — strictly linear.
