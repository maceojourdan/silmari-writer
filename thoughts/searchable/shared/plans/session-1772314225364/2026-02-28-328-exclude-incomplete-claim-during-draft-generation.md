# exclude-incomplete-claim-during-draft-generation TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/328-exclude-incomplete-claim-during-draft-generation.md`

---

## Verification (Phase 0)
The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/328-exclude-incomplete-claim-during-draft-generation.md`

Verification result:
- Result: **ALL PROPERTIES PASSED**
- States: 22 found, 11 distinct
- Exit code: 0

This TDD plan ensures code-level tests assert the same three properties per step.

---

## Tech Stack (Gate 2 – Option 1)
- Frontend/Backend: Next.js (App Router) + API Routes
- Language: TypeScript
- Validation: Zod
- Testing: Vitest (unit) + Supertest (API route integration)
- Database: Supabase (Postgres)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| api-m5g7 | endpoint | `backend/endpoints/draft/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/DraftGenerationHandler.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/draftGeneration.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/ClaimDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Claim.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/ClaimStructuralMetadataVerifier.ts` |
| db-h2s4 | service | `backend/services/DraftGenerationService.ts` |
| db-b7r2 | processor | `backend/processors/DraftAssemblyProcessor.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/DraftErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |

---

## Step 1: Receive draft generation request

- [x] **Implemented**

**From path spec:**
- Input: Draft generation HTTP request via api-m5g7 → api-n8k2
- Process: Accept and normalize request; identify Confirmed claim selection criteria
- Output: Structured draft generation command
- Error: Invalid/missing payload → standardized error (db-l1c3)

**Test** (`frontend/src/app/api/draft/generate/__tests__/route.328.test.ts`):
- [x] Reachability: POST valid payload → handler invoked → returns 200 with draft response shape
- [x] TypeInvariant: Assert normalized command matches `DraftGenerationCommand` Zod schema
- [x] ErrorConsistency: POST invalid payload → 400 with `DraftErrors328.InvalidDraftRequest`

**Implementation**:
- [x] Zod schema `ExcludeIncompleteDraftRequestSchema` in `frontend/src/server/data_structures/Claim.ts`
- [x] `DraftErrors328.InvalidDraftRequest` in `DraftErrors.ts`
- [x] `handleExcludeIncompleteDraft()` in `generateDraftHandler.ts`
- [x] API route delegates to handler (path 328 branch in `route.ts`)

---

## Step 2: Retrieve Confirmed claims

- [x] **Implemented**

**From path spec:**
- Input: DraftGenerationCommand + db-d3w8 using db-f8n5
- Process: Query for claims with status = Confirmed
- Output: Collection of Confirmed Claim entities
- Error: Data access failure → data access error (db-l1c3)

**Test** (`frontend/src/server/data_access_objects/__tests__/ClaimDAO.328.test.ts`):
- [x] Reachability: Given command → `ClaimDAO.getConfirmedClaims()` returns only `status === 'CONFIRMED'`
- [x] TypeInvariant: Returned objects conform to `ConfirmedClaim` type
- [x] ErrorConsistency: Simulate Supabase error → throws `DraftErrors328.DataAccessError`

**Implementation**:
- [x] `ConfirmedClaim` type in `frontend/src/server/data_structures/Claim.ts`
- [x] `ClaimDAO.getConfirmedClaims(sessionId)` (TDD stub)
- [x] Wrap DB failures in `DraftErrors328.DataAccessError`

---

## Step 3: Validate structural metadata completeness

- [x] **Implemented**

**From path spec:**
- Input: Collection of Confirmed claims + db-j6x9 rules
- Process: Partition into complete vs incomplete based on required metadata
- Output: `{ complete: Claim[]; incomplete: IncompleteClaimReport[] }`
- Error: If rules cannot be evaluated → log via cfg-q9c5 and treat as incomplete

**Test** (`frontend/src/server/verifiers/__tests__/ClaimStructuralMetadataVerifier.test.ts`):
- [x] Reachability: Given claims with/without required fields → correctly partitioned
- [x] TypeInvariant: Both arrays contain correct types
- [x] ErrorConsistency: Simulate rule evaluation failure → claim appears in incomplete set; logger called

**Implementation**:
- [x] `ClaimStructuralMetadataVerifier.partitionByCompleteness(claims)`
- [x] Required fields defined explicitly: `metric`, `scope`, `context`
- [x] On rule evaluation exception → log via `logger` and push to incomplete

---

## Step 4: Assemble draft from complete claims

- [x] **Implemented**

**From path spec:**
- Input: Complete claims via db-h2s4 + db-b7r2
- Process: Generate draft using only complete claims; exclude incomplete
- Output: `{ draftContent: string; omissionReport: OmissionEntry[] }`
- Error: Draft assembly fails → processing error (db-l1c3); no partial persistence

**Test** (`frontend/src/server/services/__tests__/DraftGenerationService.328.test.ts`):
- [x] Reachability: Given complete + incomplete → draft contains only complete claim IDs
- [x] TypeInvariant: Output matches `DraftGenerationResult` type
- [x] ErrorConsistency: Mock processor failure → throws `DraftErrors328.DraftAssemblyError`; assert no DB insert called

**Implementation**:
- [x] `DraftAssemblyProcessor.generateDraft(completeClaims)`
- [x] `DraftGenerationService.generateDraftExcludingIncomplete(sessionId)` orchestrates:
  1. DAO retrieval
  2. Verifier partition
  3. Processor draft generation
  4. Build omission report from incomplete set
- [x] No persistence on assembly failure

---

## Step 5: Return draft and omission notice

- [x] **Implemented**

**From path spec:**
- Input: Draft content + omission report via api-n8k2 → api-m5g7 → api-q7v1
- Process: Serialize and return HTTP response with omission notice
- Output: HTTP response containing draft + omission message
- Error: Serialization failure → log via cfg-q9c5; return standardized server error

**Test** (`frontend/src/server/request_handlers/__tests__/generateDraftHandler.328.test.ts`):
- [x] Reachability: Valid service result → HTTP 200 with `{ draft, omissions }`
- [x] TypeInvariant: Response matches frontend contract type
- [x] ErrorConsistency: Simulate service failure → `DraftErrors328.ServerError`; logger called

**Implementation**:
- [x] Response DTO `ExcludeIncompleteDraftResponse` defined in `Claim.ts`
- [x] API route wraps service result in DTO
- [x] Error wrapping for unexpected errors → `DraftErrors328.ServerError`
- [x] Frontend API contract `generateDraftExcludingIncomplete()` in `generateDraft.ts`

---

## Terminal Condition

- [x] **Implemented**

**Integration Test** (`frontend/src/server/__tests__/excludeIncompleteClaim.integration.test.ts`):

Scenario:
- DB seeded with:
  - Claim A (CONFIRMED, complete — has metric, scope, context)
  - Claim B (CONFIRMED, missing required metadata — no metric, no scope)

Execution:
- POST draft generation request with `{ sessionId }`

Assertions:
- [x] HTTP 200
- [x] Draft contains Claim A content only
- [x] Claim B ID appears in omission report
- [x] Omission message explicitly states claim omitted due to missing required structural metadata

This proves:
- [x] Reachability: Trigger → terminal condition
- [x] TypeInvariant: All boundaries respect defined schemas
- [x] ErrorConsistency: Incomplete claims excluded safely, not silently included

---

## References
- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/328-exclude-incomplete-claim-during-draft-generation.md`
- Gate 1 Requirement: `F-DRAFT-GENERATE`
- TLA+ Artifact: `ExcludeIncompleteClaimDuringDraftGeneration.tla`
