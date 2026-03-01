# record-primary-kpi-analytics-event TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/339-record-primary-kpi-analytics-event.md

---

## Verification (Phase 0)

The TLA+ model for this path passed: **Reachability, TypeInvariant, ErrorConsistency**.

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/339-record-primary-kpi-analytics-event.md
```

Verifier output:

- Result: **ALL PROPERTIES PASSED**
- States: 26 found, 13 distinct
- Exit code: 0
- Properties: Reachability, TypeInvariant, ErrorConsistency

This TDD plan ensures those same properties hold at the code level using:
- Next.js (App Router) + TypeScript
- Next.js API Routes
- Zod validation
- Supabase (Postgres)
- Vitest for unit tests

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-v3n6 | module | `frontend/modules/kpi/KpiModule.tsx` |
| ui-w8p2 | component | `frontend/components/kpi/PrimaryKpiButton.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/KpiActionVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/recordPrimaryKpi.ts` |
| api-m5g7 | endpoint | `frontend/app/api/kpi/primary/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/RecordPrimaryKpiHandler.ts` |
| db-h2s4 | service | `backend/services/PrimaryKpiService.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/PrimaryKpiVerifier.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/PrimaryKpiDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/PrimaryKpiRecord.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/KpiErrors.ts` |
| cfg-l8y1 | shared_settings | `shared/settings/analyticsProvider.ts` |
| cfg-p4b8 | shared_logging | `shared/logging/index.ts` |

---

## Step 1: User completes primary KPI action

**From path spec:**
- Input: User interaction within ui-v3n6 and ui-w8p2
- Process: Finalize KPI action and invoke api-q7v1
- Output: Validated API request sent to backend endpoint
- Error: If client-side validation fails via ui-a4y1, block action and show validation message

### Test (`frontend/components/kpi/PrimaryKpiButton.test.tsx`)

- Reachability: simulate valid click → assert `recordPrimaryKpi()` called with structured payload
- TypeInvariant: assert payload matches `RecordPrimaryKpiRequest` TypeScript type
- ErrorConsistency: simulate invalid input → assert verifier returns error and API contract not called

### Implementation

- `KpiActionVerifier.ts`: Zod schema for KPI payload
- `PrimaryKpiButton.tsx`: onClick → validate → call `recordPrimaryKpi()`
- `recordPrimaryKpi.ts`: typed `fetch('/api/kpi/primary')`

---

## Step 2: Backend endpoint receives KPI request

**From path spec:**
- Input: HTTP request to api-m5g7
- Process: api-n8k2 authenticates and delegates to service
- Output: Service invocation with structured KPI data
- Error: Validation/auth failure returns error from db-l1c3

### Test (`frontend/app/api/kpi/primary/route.test.ts`)

- Reachability: POST valid JSON → assert handler calls `PrimaryKpiService.record()`
- TypeInvariant: assert parsed body conforms to backend DTO type
- ErrorConsistency: invalid body or missing auth → assert `KpiErrors.ValidationError` with proper HTTP status

### Implementation

- `route.ts`: POST handler
- Parse body with Zod
- Call `RecordPrimaryKpiHandler.handle()`
- Map domain errors to HTTP responses

---

## Step 3: Process and persist primary KPI action

**From path spec:**
- Input: Structured KPI data in db-h2s4
- Process: Validate via db-j6x9 and persist via db-d3w8 using db-f8n5 schema
- Output: Persisted primary KPI record
- Error: Validation/persistence failure returns db-l1c3 error; no analytics emitted

### Test (`backend/services/PrimaryKpiService.test.ts`)

- Reachability: valid DTO → assert DAO `insert()` called → returns persisted record
- TypeInvariant: assert returned object matches `PrimaryKpiRecord` type
- ErrorConsistency:
  - Invalid business rule → expect `KpiErrors.DomainValidationError`
  - DAO throws → expect `KpiErrors.PersistenceError`
  - Assert analytics emitter NOT called in both error cases

### Implementation

- `PrimaryKpiVerifier.ts`: business rule validation
- `PrimaryKpiDAO.ts`: Supabase insert into `primary_kpi_events`
- `PrimaryKpiRecord.ts`: typed entity interface
- `PrimaryKpiService.ts`: orchestrates verifier + DAO

---

## Step 4: Trigger analytics event emission

**From path spec:**
- Input: Persisted KPI record
- Process: Construct analytics payload and call provider from cfg-l8y1
- Output: Analytics request sent
- Error:
  - Transformation failure → log via cfg-p4b8 and abort
  - External call fails → retry up to 3 times then log final failure

### Test (`backend/services/PrimaryKpiAnalytics.test.ts`)

- Reachability: valid record → assert `sendAnalyticsEvent()` called once
- TypeInvariant: payload matches `AnalyticsEventPayload` type
- ErrorConsistency:
  - Payload transform throws → assert logger.error called, no external call
  - External fails twice then succeeds → assert 3 attempts max
  - External fails 3 times → assert logger.error("final_failure")

### Implementation

- `analyticsProvider.ts`: exports endpoint + API key
- `PrimaryKpiService.emitAnalytics(record)`:
  - map record → payload
  - retry loop (max 3)
  - structured logging via `shared/logging`

---

## Step 5: Analytics system records and displays event

**From path spec:**
- Input: Event received by external system
- Process: External system validates and stores
- Output: Event stored and indexed
- Error: If rejected, backend logs rejection

### Test (`backend/services/PrimaryKpiAnalyticsIntegration.test.ts`)

- Reachability: mock provider returns 200 → assert service resolves success
- TypeInvariant: ensure response status handled as expected type
- ErrorConsistency: mock provider 400 rejection → assert structured log entry created

### Implementation

- Handle non-2xx responses as rejection
- Log `{ eventId, reason, status }`

---

## Step 6: User verifies analytics visibility

**From path spec:**
- Input: Indexed analytics event
- Process: Dashboard access
- Output: Visible analytics entry
- Error: If not visible, investigation via logs

### Test (`e2e/kpi-analytics.spec.ts` using Playwright)

- Reachability: complete primary KPI flow → wait for analytics mock dashboard → assert entry visible with correct user + metadata
- TypeInvariant: assert displayed data equals persisted record attributes
- ErrorConsistency: simulate provider delay → assert backend logs contain retry or failure entries

### Implementation

- Provide mock analytics dashboard page for E2E
- Expose log inspection utility for test env

---

## Terminal Condition

**Integration test** (`e2e/full-primary-kpi-flow.spec.ts`):

Exercise full path:

1. Simulate user KPI action
2. API → service → persistence
3. Analytics emission
4. Dashboard visibility

Assert:
- Primary KPI row exists in DB
- Analytics event sent once (or ≤3 retries on failure)
- Dashboard shows event with correct user identity and event attributes

This test proves:
- Reachability: trigger → dashboard
- TypeInvariant: typed boundaries at each layer
- ErrorConsistency: failures do not produce false KPI events

---

## References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/339-record-primary-kpi-analytics-event.md
- NF-KPI-LOGGING requirement (Gate 1)
- Option 1 – Next.js + Supabase tech stack
