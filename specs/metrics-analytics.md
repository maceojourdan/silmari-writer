# Metrics, Analytics & KPI Pipeline

**Domain:** Session metrics computation, leading KPI events, primary KPI tracking
**Paths:** 301, 338–339
**Priority:** P0 (338–339), P1 (301)
**Gate 1 Requirement:** NF-KPI-LOGGING

---

## Overview

After a session is finalized, a metrics pipeline computes five leading KPIs per session. Separately, onboarding completion and primary KPI actions emit analytics events to both the database and an external analytics provider.

## Primary KPI

**Writer-assisted Application → Interview Conversion Rate**
```
(interview_invitations / completed_applications) × 100
```

## Leading KPIs (per session)

| KPI | Field | Calculation |
|-----|-------|-------------|
| Time-to-first-usable-draft | `timeToFirstDraft` | `firstDraftAt - session.createdAt` (seconds) |
| Story completion rate | `completionRate` | Binary: all required slots filled = 1, else 0 |
| Truth-confirmation rate | `confirmationRate` | `confirmed_claims / total_key_claims` |
| Signal density score | `signalDensity` | Weighted sum − vagueness penalty |
| Voice session drop-off rate | `dropOff` | Binary: exited before DRAFT = true |

### Signal Density Components

| Component | Definition |
|-----------|------------|
| `num_metrics` | Count of numeric claims |
| `num_specific_tools` | Named tools/technologies |
| `num_actions` | Ordered action steps (≥3 ideal) |
| `num_artifacts` | PR/ticket/doc references |
| `alignment_hits` | Required skills mentioned |
| `vagueness_penalty` | "helped", "worked on", "involved" without specifics |

## API Endpoints

| Method | Path | Request | Response | Error Codes |
|--------|------|---------|----------|-------------|
| `POST` | `/api/onboarding/complete` | `{ userId, step, metadata }` | `{ status, analyticsRecorded }` | 400, 401, 409, 422, 500 |
| `POST` | `/api/kpi/primary` | `{ userId, actionType, timestamp, metadata }` | `{ status: "PERSISTED", eventId }` | 400, 401, 422, 500 |

## Metrics Pipeline (Path 301)

```
Session FINALIZED
  → Step 1: validate sessionId (UUID)
  → Step 2: load session + events (abort if not FINALIZED)
  → Step 3: compute 5 metrics (pure functions)
  → Step 4: upsert session_metrics (Supabase)
  → Step 5: log pipeline success
```

Implemented as `StoreSessionMetricsProcessChain.run(sessionId)`. Strictly linear, no feedback loops.

## Leading KPI Pipeline (Path 338)

```
POST /api/onboarding/complete-step
  → validate + authenticate
  → OnboardingCompletionProcessor.process()
  → isEligible() + updateOnboardingStep()
  → construct AnalyticsEvent { kpiId: LeadingKpis.ONBOARDING_STEP_1 }
  → insertAnalyticsEvent() [non-fatal on failure]
  → return { analyticsRecorded: boolean }
```

## Primary KPI Pipeline (Path 339)

```
POST /api/kpi/primary
  → validate + authenticate
  → PrimaryKpiVerifier.validate()
  → PrimaryKpiDAO.insert() → PrimaryKpiRecord
  → PrimaryKpiService.emitAnalytics(record) [retry ≤3, non-fatal]
  → return { status: "PERSISTED", eventId }
```

## Database Entities

| Table | Key Fields |
|-------|------------|
| `session_metrics` | `id`, `session_id` (unique), `time_to_first_draft`, `completion_rate`, `confirmation_rate`, `signal_density`, `drop_off`, `computed_at` |
| `events` | `id`, `session_id`, `event_type`, `occurred_at`, `payload` |
| `analytics_events` | `id`, `kpi_id`, `user_id`, `timestamp`, `metadata` |
| `primary_kpi_events` | `id`, `user_id`, `action_type`, `timestamp`, `status`, `metadata` |
| `onboarding` | `user_id`, `step_1_completed_at`, `current_step` |

## Error Catalog

| Code | HTTP | Condition |
|------|------|-----------|
| `InvalidSessionIdentifierError` | 400 | Bad UUID |
| `SessionNotFoundError` | 404 | Session missing |
| `SessionNotCompletedError` | 409 | Status not FINALIZED |
| `InvalidMetricsInputError` | 422 | Required timestamps missing |
| `MetricsPersistenceError` | 500 | Supabase upsert failure |
| `STEP_ALREADY_COMPLETED` | 409 | Onboarding idempotency |
| `KPI_IDENTIFIER_MISSING` | 422 | LeadingKpis constant unresolved |
| `KpiErrors.PersistenceError` | 500 | DAO insert failure |

## Known Deviations

| ID | Description | Severity |
|----|-------------|----------|
| DEV-339-2 | Response status always 'PERSISTED'; updateStatus('ANALYTICS_SENT') result discarded | Medium |
| DEV-339-3 | Final-failure log lacks structured fields for reason/status | Low |
| DEV-339-4 | KpiActionVerifier uses imperative checks instead of unified Zod schema | Low |

---

*Source: TDD plans 301, 338–339 (session-1772314225364). All paths TLA+ verified.*
