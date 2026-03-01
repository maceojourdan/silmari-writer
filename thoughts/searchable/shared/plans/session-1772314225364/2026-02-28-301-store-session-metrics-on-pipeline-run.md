# store-session-metrics-on-pipeline-run TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/301-store-session-metrics-on-pipeline-run.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/301-store-session-metrics-on-pipeline-run.md
```

Verifier output:

- Result: **ALL PROPERTIES PASSED**
- States: 22 found, 11 distinct
- Exit code: 0

This TDD plan mirrors those three properties as code-level assertions for each step.

---

## Tech Stack (Gate 2)

- Backend: Next.js API Routes + Server Actions (Node.js, TypeScript)
- Validation: Zod
- Testing: Vitest (or Vitest equivalent in Next.js repo)
- Database: Supabase (PostgreSQL)

All implementations live inside the Next.js backend layer.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| mq-r4z8 | backend_process_chain | `backend/process_chains/StoreSessionMetricsProcessChain.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/SessionMetricsDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Session.ts`, `Event.ts`, `SessionMetrics.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/SessionMetricsVerifier.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/MetricsErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/metricsLogger.ts` |

---

## Step 1: Trigger metrics process chain [x]

**From path spec:**
- Input: Completed session identifier emitted to backend_process_chain (mq-r4z8)
- Process: Initiate the metrics computation workflow for the specified completed session
- Output: Metrics computation job context containing session identifier
- Error: If session identifier is missing or malformed, raise error defined in backend_error_definitions (db-l1c3) and abort processing

### Test
`backend/process_chains/__tests__/StoreSessionMetricsProcessChain.step1.test.ts`

- Reachability:
  - Call `start(sessionId)` with valid UUID
  - Assert returned `{ sessionId }` job context
- TypeInvariant:
  - Assert `jobContext.sessionId` is string (UUID format)
- ErrorConsistency:
  - Call with `undefined` or malformed ID
  - Expect `InvalidSessionIdentifierError`

### Implementation
`backend/process_chains/StoreSessionMetricsProcessChain.ts`

- Export `start(sessionId: string)`
- Validate UUID via Zod
- On failure throw `InvalidSessionIdentifierError` from `MetricsErrors.ts`
- Return `{ sessionId }`

---

## Step 2: Load session and event data [x]

**From path spec:**
- Input: Session identifier from job context; data via DAO (db-d3w8) from data_structure (db-f8n5)
- Process: Fetch session core data and associated event records
- Output: Aggregated session dataset
- Error: If session not found or not marked completed, raise error and terminate

### Test
`backend/process_chains/__tests__/StoreSessionMetricsProcessChain.step2.test.ts`

- Reachability:
  - Mock `SessionMetricsDAO.getSessionWithEvents(sessionId)`
  - Provide completed session + events
  - Assert aggregated dataset returned
- TypeInvariant:
  - Assert dataset includes `{ session: { status: 'FINALIZED' }, events: Event[] }`
- ErrorConsistency:
  - DAO returns null → expect `SessionNotFoundError`
  - Session status !== FINALIZED → expect `SessionNotCompletedError`

### Implementation
- Add method `loadSessionData(jobContext)`
- DAO method:
  - Query `sessions` table
  - Query `events` table by session_id
- Validate status === `FINALIZED`
- Throw errors from `MetricsErrors.ts`

---

## Step 3: Compute session metrics [x]

**From path spec:**
- Input: Aggregated session dataset
- Process: Calculate:
  - time-to-first-draft
  - completion rate
  - confirmation rate
  - signal density
  - drop-off
- Output: Session metrics object
- Error: If required data missing/invalid, validate via backend_verifier and raise error

### Test
`backend/process_chains/__tests__/StoreSessionMetricsProcessChain.step3.test.ts`

- Reachability:
  - Provide valid dataset with timestamps + events
  - Assert metrics object contains all five fields
- TypeInvariant:
  - Assert numeric fields:
    - `timeToFirstDraft: number`
    - `completionRate: number`
    - `confirmationRate: number`
    - `signalDensity: number`
    - `dropOff: number`
- ErrorConsistency:
  - Provide dataset missing required timestamps
  - Expect `InvalidMetricsInputError`

### Implementation
`backend/verifiers/SessionMetricsVerifier.ts`

- Zod schema requiring:
  - session.createdAt
  - firstDraftAt
  - finalizedAt
  - required event categories
- `computeMetrics(dataset)`:
  - Implement pure functions for each metric
  - Validate input with verifier
  - Throw errors from `MetricsErrors.ts` if invalid

---

## Step 4: Persist metrics record [x]

**From path spec:**
- Input: Session metrics object; persistence via DAO into data_structure
- Process: Store or update metrics record
- Output: Persisted metrics record linked to session
- Error: If database write fails, log and raise persistence error

### Test
`backend/process_chains/__tests__/StoreSessionMetricsProcessChain.step4.test.ts`

- Reachability:
  - Mock DAO `upsertSessionMetrics`
  - Return persisted record
  - Assert returned record includes sessionId + metric fields
- TypeInvariant:
  - Assert persisted object matches `SessionMetrics` structure
- ErrorConsistency:
  - Mock DAO to throw
  - Expect:
    - logger called
    - `MetricsPersistenceError` thrown

### Implementation
`backend/data_access_objects/SessionMetricsDAO.ts`

- `upsertSessionMetrics(metrics)` → Supabase upsert
- Wrap DB call in try/catch
- On error:
  - Log via `metricsLogger.error`
  - Throw `MetricsPersistenceError`

---

## Step 5: Mark metrics pipeline success [x]

**From path spec:**
- Input: Persisted metrics record confirmation
- Process: Record successful completion for observability
- Output: System state reflecting success
- Error: If confirmation cannot be recorded, log and raise operational error

### Test
`backend/process_chains/__tests__/StoreSessionMetricsProcessChain.step5.test.ts`

- Reachability:
  - Call `markSuccess(persistedMetrics)`
  - Assert success flag returned `{ status: 'SUCCESS' }`
- TypeInvariant:
  - Assert returned state includes `sessionId` and `status`
- ErrorConsistency:
  - Mock logger failure or state write failure
  - Expect `MetricsPipelineOperationalError`

### Implementation
- `markSuccess(record)` inside process chain
- Log via `metricsLogger.info`
- Optionally write pipeline_execution table entry
- Throw operational error if logging/state write fails

---

## Terminal Condition [x]

**Integration Test**  
`backend/process_chains/__tests__/StoreSessionMetricsProcessChain.integration.test.ts`

- Seed DB with:
  - Completed session
  - Events covering draft, verify, finalize
- Execute:

```ts
await StoreSessionMetricsProcessChain.run(sessionId)
```

- Assert:
  - `session_metrics` row exists
  - Contains:
    - time-to-first-draft
    - completion rate
    - confirmation rate
    - signal density
    - drop-off

This proves Reachability from trigger to terminal condition.

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/301-store-session-metrics-on-pipeline-run.md`
- Gate 1 Requirement: `NF-KPI-LOGGING`
- Gate 2 Stack: Option 1 – Next.js + Supabase
