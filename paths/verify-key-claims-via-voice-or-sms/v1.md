# PATH: verify-key-claims-via-voice-or-sms

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

System detects that all Key claims (metrics, scope, production, security details) are collected and marked as unverified and initiates a verification request to the claimant

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `db-f8n5` | data_structure | Stores key claim records, verification status, and contact details. |
| `db-d3w8` | data_access_object | Handles retrieval and persistence of claim and verification records. |
| `db-j6x9` | backend_verifier | Validates completeness and eligibility of claims before verification. |
| `db-l1c3` | backend_error_definitions | Defines structured error handling for verification and persistence failures. |

## Steps

1. **Detect unverified key claims**
   - Input: Key claims stored with unverified status in db-f8n5 via db-d3w8
   - Process: Evaluate whether all required claim categories (metrics, scope, production, security details) are present and currently marked as unverified but eligible for verification.
   - Output: Verification eligibility flag and list of claim items requiring confirmation.
   - Error: If required claim categories are missing or data is malformed, raise validation error via db-j6x9 and halt verification initiation.

2. **Initiate voice or SMS verification request**
   - Input: Verification eligibility flag and claimant contact details from db-f8n5
   - Process: Trigger a verification workflow that sends a voice call or SMS containing the claims summary and a request for confirmation.
   - Output: Verification request record with pending status and external delivery attempt logged.
   - Error: If contact details are invalid or external delivery fails, log and classify error using db-l1c3 and retry up to 3 times before marking verification as failed.

3. **Receive and validate claimant confirmation**
   - Input: Inbound confirmation response linked to pending verification request
   - Process: Match the confirmation to the original request and validate that all listed claim items are explicitly confirmed.
   - Output: Confirmation result indicating full confirmation of all claim items.
   - Error: If confirmation is partial, ambiguous, expired, or mismatched, update verification request as failed using db-l1c3 and, if retry limit not exceeded, re-initiate verification (max 3 attempts).

4. **Mark claims as verified**
   - Input: Full confirmation result and associated claim records in db-f8n5
   - Process: Update each claim record status from unverified to verified and persist the changes.
   - Output: All claim records updated with verified status and timestamp.
   - Error: If persistence fails or a claim record cannot be updated, raise data access error via db-l1c3 and prevent drafting from proceeding.

5. **Enable drafting process**
   - Input: Verified claim records from db-f8n5
   - Process: Evaluate drafting prerequisites and lift any verification-based restrictions, allowing the drafting workflow to continue.
   - Output: Drafting interface state updated to enabled and verification status visibly set to "Verified" for all claims.
   - Error: If drafting state cannot be updated due to inconsistent verification state, log error via db-l1c3 and keep drafting disabled until resolved.

## Terminal Condition

User sees all Key claims marked as "Verified" in the drafting interface and the drafting process is enabled for continuation

## Feedback Loops

If verification confirmation is not received or is incomplete, the system retries the voice/SMS verification request up to 3 times before marking verification as failed and surfacing an error to the user.
