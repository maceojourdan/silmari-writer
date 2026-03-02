# Draft Generation & Review

**Domain:** Draft generation from confirmed claims, review workflow, session approval, finalization
**Paths:** 298–300, 325–329
**Priority:** P0

---

## Overview

Once claims are verified, the Drafter (LLM-C) generates a structured answer draft using only confirmed claims. The user reviews, approves, and the system finalizes the draft. Uncertain claims are hedged or omitted. Denied claims never appear.

## State Machine

```
VERIFY ──(all key claims resolved)──→ DRAFT ──→ REVIEW ──→ FINALIZE
                                                   │
                                                   └── "not accurate" ──→ RECALL
```

### Draft Entity Status
```
(none) → DRAFT → APPROVED → FINALIZED
```

### Content Entity Status (Review Workflow)
```
DRAFT → REVIEW → APPROVED → FINALIZE
```

## API Endpoints

| Method | Path | Request | Response | Error Codes |
|--------|------|---------|----------|-------------|
| `POST` | `/api/generate-draft` | `{ claimSetId: uuid }` | `{ draft, claimsUsed[] }` | 400, 404, 422, 500 |
| `POST` | `/api/draft/generate` | `{ caseId }` or `{ storyRecordId }` or `{ sessionId }` | Draft with claims | 400, 500 |
| `POST` | `/api/sessions/[id]/approve` | Path param `id` | `{ state: 'FINALIZE' }` | 400, 404, 409, 500 |
| `POST` | `/api/finalize` | `{ draftId, userId }` | `{ artifact, finalized, metricsLogged }` | 400, 404, 422, 500 |
| `POST` | `/api/review/approve` | `{ contentId }` | `{ workflowStage }` | 400, 401, 404, 422, 500 |

## Claim Filtering Pipeline

Claims pass through three sequential filters before draft generation:

### Filter 1 — Confirmation Status
- **Include:** `status === 'confirmed'` or `confirmed === true`
- **Exclude:** unconfirmed, rejected, denied
- **Hard claims** without confirmation metadata are silently dropped
- **Empty set:** throws `NO_CONFIRMED_CLAIMS`, aborts generation

### Filter 2 — Structural Metadata Completeness
- Required fields: `metric`, `scope`, `context`
- Incomplete claims excluded and added to `omissionReport`
- Non-fatal; generation continues with remaining claims

### Filter 3 — Document Structure Validation
- Claims grouped by section: `context`, `actions`, `outcome`
- Unrecognized section → `TRANSFORMATION_ERROR`
- Missing required section → `TRANSFORMATION_ERROR`

## LLM Contract — Drafter (LLM-C)

**Inputs:** StoryRecord with truth_checks, job_object, question_object, draft_template, filtered claims

**Output (strict JSON):**
```ts
{
  draft_text: string;
  bullets_of_supporting_evidence: string[];
  claims_used: Array<{ id: string, status: 'confirmed' | 'uncertain' }>;
  suggested_verification_sms: string[]; // max 3
}
```

**Hard Rules:**
1. Confirmed claims stated as fact
2. Uncertain claims hedged: "approximately", "I estimate"
3. Denied claims never appear
4. No fabrication of metrics, tools, dates, outcomes
5. Answer length within configurable limits
6. Every statement maps to a `claims_used` entry

## UI Components

| Component | Props | Purpose |
|-----------|-------|---------|
| `GenerateDraftButton` | `claimSetId` | Trigger draft generation with section preview |
| `DraftGenerator` | `caseId` | Case-based draft generation |
| `DraftGeneratorButton` | `storyRecordId` | Story-based draft with precondition check |
| `ApproveButton` | `sessionId, sessionState` | Session approval with state guard |
| `ReviewScreen` | `selectedContentId?` | Review + approve + voice edit + return to recall |
| `DraftModule` | — | Wraps DraftGeneratorButton, interprets NO_CONFIRMED_CLAIMS |

## Database Entities

| Table | Key Fields |
|-------|------------|
| `drafts` | `id`, `status`, `content`, `claims_used[]`, `interaction_data`, `export_artifact` |
| `sessions` | `id`, `status`, `draft_text`, `truth_checks`, `draft_versions[]`, `metrics` |
| `content` | `id`, `status`, `workflow_stage`, `body` |
| `approval_log` | `session_id`, `action`, `timestamp` |

## Error Catalog

| Code | HTTP | Condition |
|------|------|-----------|
| `INVALID_PARAMETERS` | 400 | Zod validation failure |
| `NO_CONFIRMED_CLAIMS` | 400/422 | All claims unconfirmed/rejected |
| `CLAIM_SET_NOT_FOUND` | 404 | Referenced claim set missing |
| `INVALID_STATE_TRANSITION` | 409 | Session not in DRAFT state |
| `TRANSFORMATION_ERROR` | 422 | Missing required document section |
| `GENERATION_FAILED` | 500 | LLM-C failure |
| `PERSISTENCE_FAILED` | 500 | Draft persistence failure |

---

*Source: TDD plans 298–300, 325–329 (session-1772314225364). All paths TLA+ verified.*
