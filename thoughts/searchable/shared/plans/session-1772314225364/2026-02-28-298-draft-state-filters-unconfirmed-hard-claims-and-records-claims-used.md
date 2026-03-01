# draft-state-filters-unconfirmed-hard-claims-and-records-claims-used TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used.md`

Tech Stack (Gate 2 – Option 1):
- Backend: Next.js API Routes + Server Actions (Node.js, TypeScript)
- Validation: Zod
- Testing: Vitest (or Vitest) in Node environment
- DB: Supabase (PostgreSQL)

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used.md
```

Verification output:
- Result: ALL PROPERTIES PASSED
- States: 26 found, 13 distinct
- Exit code: 0

This TDD plan maps those proven properties directly to code-level tests.

---

## Resource Mapping

| UUID     | Registry Name              | Concrete Implementation |
|----------|---------------------------|--------------------------|
| db-f8n5  | data_structure            | `backend/data_structures/StoryRecord.ts` (Zod schema + TS type) |
| db-d3w8  | data_access_object        | `backend/data_access_objects/StoryRecordDAO.ts` |
| db-h2s4  | service                   | `backend/services/DraftService.ts` |
| db-j6x9  | backend_verifier          | `backend/verifiers/TruthCheckVerifier.ts` |
| db-l1c3  | backend_error_definitions | `backend/error_definitions/DraftErrors.ts` |
| mq-r4z8  | backend_process_chain     | `backend/process_chains/DraftProcessChain.ts` |
| api-n8k2 | request_handler           | `backend/request_handlers/DraftRequestHandler.ts` |

---

## Step 1: Trigger DRAFT execution ✅

**From path spec:**
- Input: StoryRecord containing truth_checks, invoked via backend_process_chain
- Process: Detect DRAFT state and initiate drafting
- Output: DRAFT execution context
- Error: If StoryRecord missing or not in DRAFT state → domain error (db-l1c3)

### Test (`backend/process_chains/__tests__/DraftProcessChain.step1.test.ts`)

- Reachability:
  - Given a StoryRecord in `DRAFT` state
  - When `DraftProcessChain.execute(recordId)` is called
  - Then returns execution context containing StoryRecord and truth_checks

- TypeInvariant:
  - Assert returned object matches `DraftExecutionContext` type
  - Assert `context.storyRecord.truth_checks` is defined array

- ErrorConsistency:
  - Given no StoryRecord → expect `DraftStateError.STORY_NOT_FOUND`
  - Given StoryRecord in non-DRAFT state → expect `DraftStateError.INVALID_STATE`

### Implementation (`backend/process_chains/DraftProcessChain.ts`)

- Export `execute(storyRecordId: string)`
- Use `StoryRecordDAO.findById`
- Validate `status === 'DRAFT'`
- Throw typed errors from `DraftErrors.ts`
- Return `{ storyRecordId }` as initial context

---

## Step 2: Load full StoryRecord with truth checks ✅

**From path spec:**
- Input: StoryRecord identifier; DAO
- Process: Retrieve persisted StoryRecord including truth_checks
- Output: Complete StoryRecord entity
- Error: Retrieval failure or malformed truth_checks → error

### Test (`backend/data_access_objects/__tests__/StoryRecordDAO.step2.test.ts`)

- Reachability:
  - Given persisted StoryRecord with truth_checks
  - When `findById` is called
  - Then full entity returned

- TypeInvariant:
  - Validate against `StoryRecordSchema.parse()`

- ErrorConsistency:
  - Simulate DB failure → expect `DraftDataAccessError.RETRIEVAL_FAILED`
  - Provide malformed truth_checks → expect `DraftValidationError.MALFORMED_TRUTH_CHECKS`

### Implementation (`backend/data_access_objects/StoryRecordDAO.ts`)

- `findById(id: string): Promise<StoryRecord>`
- Supabase query
- Zod parse via `StoryRecordSchema`
- Map DB errors to DraftErrors

---

## Step 3: Filter unconfirmed hard claims ✅

**From path spec:**
- Input: StoryRecord with truth_checks
- Process: Exclude unconfirmed hard claims
- Output: Filtered claim set
- Error: Missing confirmation metadata → treat as unconfirmed; invalid structure → validation error

### Test (`backend/services/__tests__/DraftService.step3.test.ts`)

- Reachability:
  - Given StoryRecord with:
    - confirmed hard claim
    - unconfirmed hard claim
    - soft claim
  - When `filterConfirmedClaims(record)`
  - Then only confirmed hard + allowed claims returned

- TypeInvariant:
  - Assert output is `FilteredClaimSet` type

- ErrorConsistency:
  - Claim missing confirmation metadata → excluded (not thrown)
  - Invalid truth_check structure → expect `DraftValidationError.INVALID_TRUTH_CHECK`

### Implementation (`backend/services/DraftService.ts`)

- `filterConfirmedClaims(record: StoryRecord)`
- Use `TruthCheckVerifier.validateStructure`
- Hard claims: include only `status === 'confirmed'`
- Missing metadata → exclude
- Throw validation error if structure invalid

---

## Step 4: Generate draft text and claims_used metadata ✅

**From path spec:**
- Input: Filtered claim set
- Process: Compose draft_text and generate claims_used
- Output: Draft payload
- Error: Service-level error if generation fails

### Test (`backend/services/__tests__/DraftService.step4.test.ts`)

- Reachability:
  - Given filtered claim set
  - When `generateDraft(filteredClaims)`
  - Then returns `{ draft_text, claims_used }`

- TypeInvariant:
  - `draft_text` is string
  - `claims_used` is string[] of claim IDs

- ErrorConsistency:
  - Simulate generation failure → expect `DraftServiceError.GENERATION_FAILED`

### Implementation (`backend/services/DraftService.ts`)

- `generateDraft(filteredClaims)`
- Deterministic template composition (no LLM in unit test)
- `claims_used = filteredClaims.map(c => c.id)`
- Wrap failures in DraftServiceError

---

## Step 5: Persist draft and metadata ✅

**From path spec:**
- Input: Draft payload; DAO
- Process: Update StoryRecord
- Output: Persisted StoryRecord
- Error: Persistence failure → data access error; no partial commit

### Test (`backend/data_access_objects/__tests__/StoryRecordDAO.step5.test.ts`)

- Reachability:
  - Given draft payload
  - When `updateDraft(id, draftPayload)`
  - Then DB updated and returned entity contains draft_text and claims_used

- TypeInvariant:
  - Returned entity passes `StoryRecordSchema`

- ErrorConsistency:
  - Simulate DB failure → expect `DraftDataAccessError.PERSISTENCE_FAILED`
  - Ensure no partial update (mock transaction rollback assertion)

### Implementation (`backend/data_access_objects/StoryRecordDAO.ts`)

- `updateDraft(id, payload)`
- Supabase update within transaction
- On error → throw DraftDataAccessError

---

## Step 6: Return updated draft to caller ✅

**From path spec:**
- Input: Persisted StoryRecord
- Process: Transform to response
- Output: Response payload with draft_text and claims_used
- Error: Transformation failure → API error

### Test (`backend/request_handlers/__tests__/DraftRequestHandler.step6.test.ts`)

- Reachability:
  - Given persisted StoryRecord
  - When `handleDraftRequest(id)`
  - Then returns response with draft_text excluding unconfirmed hard claims

- TypeInvariant:
  - Response matches `DraftResponseSchema`

- ErrorConsistency:
  - Simulate transform failure → expect `DraftApiError.RESPONSE_TRANSFORM_FAILED`

### Implementation (`backend/request_handlers/DraftRequestHandler.ts`)

- Call `DraftProcessChain.execute`
- Map StoryRecord → `{ draft_text, claims_used }`
- Validate via Zod response schema
- Throw API-level error if mapping fails

---

## Terminal Condition ✅

### Integration Test (`backend/__tests__/DraftProcessChain.integration.test.ts`)

- Given StoryRecord with:
  - confirmed hard claim A
  - unconfirmed hard claim B
- When full process chain executed
- Then:
  - draft_text contains claim A
  - draft_text does NOT contain claim B
  - claims_used includes only A
  - Persisted StoryRecord reflects same

This proves:
- Reachability: Trigger → terminal
- TypeInvariant: All step boundaries validated
- ErrorConsistency: All error branches mapped to structured DraftErrors

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used.md`
- Gate 1 Requirement: `F-DRAFT-GENERATE`
- TLA+ Spec: `DraftStateFiltersUnconfirmedHardClaimsAndRecordsClaimsUsed.tla`
