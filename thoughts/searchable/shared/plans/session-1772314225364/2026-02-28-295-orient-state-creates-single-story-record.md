# orient-state-creates-single-story-record TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/295-orient-state-creates-single-story-record.md`

Tech stack (Gate 2 – Option 1):
- Next.js (App Router) + TypeScript
- Next.js API Routes / Server Actions (Node.js runtime)
- Zod for validation
- Supabase (Postgres)
- Vitest or Vitest for testing

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/295-orient-state-creates-single-story-record.md
```

Result (from verification_results_json):
- Result: ALL PROPERTIES PASSED
- States: 22 found, 11 distinct
- Exit code: 0

This guarantees at the model level that:
- Every step is reachable from the ORIENT trigger
- Input/output types are consistent at each boundary
- All error branches produce valid error states

The following TDD plan reproduces those guarantees at code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| mq-r4z8 | backend_process_chain | `frontend/src/server/process_chains/OrientProcessChain.ts` |
| db-f8n5 | data_structure | `frontend/src/server/data_structures/OrientStoryRecord.ts` (Zod + TS type) |
| db-j6x9 | backend_verifier | `frontend/src/server/verifiers/StoryRecordVerifier.ts` |
| db-d3w8 | data_access_object | `frontend/src/server/data_access_objects/OrientStoryRecordDAO.ts` |
| api-n8k2 | request_handler | `frontend/src/server/request_handlers/CreateStoryRecordHandler.ts` |
| db-l1c3 | backend_error_definitions | `frontend/src/server/error_definitions/OrientErrors.ts` |

---

## Step 1: Trigger ORIENT process chain ✅

**From path spec:**
- Input: ORIENT state execution event with multiple candidate experiences (mq-r4z8)
- Process: Activates the ORIENT backend process chain and passes experiences as input context
- Output: ORIENT execution context containing candidate experiences
- Error: If process chain not registered or fails to start → system error (db-l1c3)

### Test (`backend/process_chains/__tests__/OrientProcessChain.test.ts`)

- Reachability:
  - Call `startOrientProcess({ experiences: [...] })`
  - Assert returned context contains `experiences`
- TypeInvariant:
  - Assert returned object matches `OrientExecutionContext` type
  - Assert `experiences` is `Experience[]`
- ErrorConsistency:
  - Simulate unregistered chain (e.g., internal registry lookup fails)
  - Assert thrown/returned `BackendError` with code `SYSTEM_PROCESS_CHAIN_NOT_FOUND`

### Implementation (`backend/process_chains/OrientProcessChain.ts`)

- Export `startOrientProcess(input: OrientEvent): OrientExecutionContext`
- Internally validate chain registration (static registry map)
- Return `{ experiences }` as execution context
- On missing chain → return/throw `BackendError.system(...)`

---

## Step 2: Select single experience and derive story data ✅

**From path spec:**
- Input: ORIENT execution context with multiple experiences
- Process: Select exactly one experience and derive `story_title` + `initial_context`
- Output: Story creation payload
- Error: If no valid experience can be selected → domain validation error

### Test (`backend/process_chains/__tests__/OrientSelectExperience.test.ts`)

- Reachability:
  - Provide execution context from Step 1
  - Assert returned payload has `story_title` and `initial_context`
- TypeInvariant:
  - Assert payload matches `StoryCreationPayload` type
  - Assert `story_title: string`, `initial_context: object`
- ErrorConsistency:
  - Provide empty or invalid experiences
  - Assert `BackendError` with code `NO_VALID_EXPERIENCE_SELECTED`

### Implementation (`backend/process_chains/OrientProcessChain.ts`)

- Add function `selectExperience(context: OrientExecutionContext)`
- Business rule (minimal for path): select first valid experience
- Derive:
  - `story_title = experience.title`
  - `initial_context = { experienceId, summary }`
- If none valid → return `BackendError.domain(...)`

---

## Step 3: Validate StoryRecord structure ✅

**From path spec:**
- Input: Story creation payload (db-f8n5, db-j6x9)
- Process: Apply backend verifier rules
- Output: Validated StoryRecord entity
- Error: Validation error, no record created

### Test (`backend/verifiers/__tests__/StoryRecordVerifier.test.ts`)

- Reachability:
  - Call `validateStoryRecord(payload)`
  - Assert returns validated `StoryRecord`
- TypeInvariant:
  - Assert result satisfies Zod schema from `StoryRecord.ts`
- ErrorConsistency:
  - Omit `story_title`
  - Assert `BackendError` with code `STORY_RECORD_VALIDATION_FAILED`
  - Assert no DAO insert called (mock DAO)

### Implementation

**`backend/data_structures/StoryRecord.ts`**
- Zod schema:
  - id (optional before persistence)
  - story_title: string (non-empty)
  - initial_context: object (required)

**`backend/verifiers/StoryRecordVerifier.ts`**
- Function `validateStoryRecord(payload)`
- Use Zod `.parse()`
- Catch and wrap in `BackendError.validation(...)`

---

## Step 4: Persist StoryRecord ✅

**From path spec:**
- Input: Validated StoryRecord
- Process: Insert exactly one new StoryRecord
- Output: Persisted StoryRecord with unique identifier
- Error: Persistence error, no partial record remains

### Test (`backend/data_access_objects/__tests__/StoryRecordDAO.test.ts`)

- Reachability:
  - Mock Supabase client
  - Call `insertStoryRecord(validRecord)`
  - Assert one insert
  - Assert returned record has `id`
- TypeInvariant:
  - Assert returned object matches `StoryRecord` with `id: string`
- ErrorConsistency:
  - Simulate DB error
  - Assert `BackendError` with code `STORY_RECORD_PERSISTENCE_FAILED`
  - Assert no partial state (mock ensures no commit on failure)

### Implementation (`backend/data_access_objects/StoryRecordDAO.ts`)

- Function `insertStoryRecord(record: StoryRecord)`
- Use Supabase `.insert().select().single()`
- Wrap DB errors into `BackendError.persistence(...)`

---

## Step 5: Return StoryRecord to interface ✅

**From path spec:**
- Input: Persisted StoryRecord (api-n8k2)
- Process: Format and return via request handler
- Output: API response containing created StoryRecord
- Error: If formatting/transmission fails → structured backend error

### Test (`backend/request_handlers/__tests__/CreateStoryRecordHandler.test.ts`)

- Reachability:
  - Mock process chain → validator → DAO
  - Call handler with ORIENT event
  - Assert HTTP 200 with StoryRecord JSON
- TypeInvariant:
  - Assert response body includes `id`, `story_title`, `initial_context`
- ErrorConsistency:
  - Simulate formatting failure or thrown error
  - Assert HTTP 500 with structured `BackendError` payload

### Implementation

**`backend/request_handlers/CreateStoryRecordHandler.ts`**
- Orchestrates:
  1. `startOrientProcess`
  2. `selectExperience`
  3. `validateStoryRecord`
  4. `insertStoryRecord`
- Return `NextResponse.json(record)`
- Catch errors → map to structured error response

---

## Terminal Condition ✅

**Integration test** (`backend/__tests__/orient.integration.test.ts`)

- Exercise full path from ORIENT trigger:
  - Input: multiple candidate experiences
  - Call HTTP endpoint (Next.js API route)
- Assert:
  - HTTP 200
  - Exactly one StoryRecord inserted
  - Returned object contains visible `story_title` and `initial_context`

This proves:
- Reachability: full path executable end-to-end
- TypeInvariant: types preserved across all boundaries
- ErrorConsistency: failures return structured errors without partial records

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/295-orient-state-creates-single-story-record.md`
- Gate 1: F-ORIENT-STORY
- TLA+ artifact: `frontend/artifacts/tlaplus/295-orient-state-creates-single-story-record/OrientStateCreatesSingleStoryRecord.tla`
