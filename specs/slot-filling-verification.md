# Slot Filling & Verification

**Domain:** Claim extraction, truth-check confirmation, verification pipeline, drafting gate
**Paths:** 296–297, 317–324
**Priority:** P0

---

## Overview

After voice recall fills slots, the system extracts claims from transcripts, identifies key claims requiring confirmation (metrics, scope, production, security), and presents them to the user. Claims are confirmed/denied via voice or SMS. Verification completeness gates the transition from VERIFY to DRAFT state.

## State Machine

```
RECALL ──(minimum slots met)──→ VERIFY ──(all key claims confirmed/uncertain)──→ DRAFT
```

### Verification Sub-states
```
[Claims extracted] → Key claims identified → User confirms/denies each
                                                ├─ all confirmed → DRAFT
                                                ├─ some uncertain → DRAFT (with hedging)
                                                └─ incomplete → re-prompt
```

### Claim Status Transitions
```
(presented) → confirmed   [user selects Y]
(presented) → denied      [user selects N]
(presented) → uncertain   [user skips / timeout]
unverified  → verified    [full confirmation received]
unverified  → not_verified [SMS dispute]
pending     → timed_out   [no response within window]
```

## API Endpoints

| Method | Path | Request | Response | Error Codes |
|--------|------|---------|----------|-------------|
| `POST` | `/api/behavioral-question/evaluate` | `BehavioralQuestionDraft` | `{ eligible: true }` | 400, 500 |
| `POST` | `/api/truth-checks/confirm` | `{ claim_id, status, source }` | `{ claim_id, status, source }` | 400, 500 |
| `POST` | `/api/verification/initiate` | `{ claimantId: uuid }` | `{ verificationStatus, draftingAllowed }` | 400, 404, 500 |
| `POST` | `/api/sms/dispute` | `SmsDisputePayloadSchema` | `{ claimantId, disputedClaimIds }` | 400, 404, 409, 500 |
| `GET` | `/api/claims/[claimId]/status` | — | `{ claimStatus, draftingStatus, timedOut? }` | 400, 500 |

## Minimum Slot Requirements

### Behavioral/STAR
| Slot | Requirement |
|------|------------|
| `objective` | Required |
| `actions` | Min 3 steps |
| `obstacles` | Min 1 |
| `outcome` | Required (≥1 metric OR ≥2 qualitative) |
| `roleClarity` | Required |

### Technical
| Slot | Requirement |
|------|------------|
| `problem_statement` | Required |
| `environment` | Required (prod vs non-prod) |
| `approach` | Min 3 steps |
| `tools_tech` | Required |
| `validation` | Required |
| `outcome` | Required |

### Motivation/Culture
| Slot | Requirement |
|------|------------|
| `reason` | Aligned to job/company |
| `examples` | 1–2 specific from past |
| `values_statement` | Grounded in behavior |

## Claim Categories Requiring Confirmation

| Category | Examples |
|----------|---------|
| `metrics` | "30%", "$X", "reduced time by Y" |
| `scope` | "led team", "owned architecture" |
| `production` | Production environment claims |
| `security` | Security/compliance claims |

## UI Components

| Component | Props | Purpose |
|-----------|-------|---------|
| `BehavioralQuestionForm` | `sessionId` | Objective/actions/obstacles/outcome/roleClarity form |
| `ConfirmMetricClaim` | `claimId, source` | Y/N toggle for claim confirmation |
| `ClaimStatusPanel` | `data, loading, error` | Displays claim + drafting status with timeout badge |
| `VerificationStatusModule` | `verificationStatus, draftingAllowed` | Drafting gate UI |
| `DraftingBlockedAccessControl` | `CaseStateResponse` | Renders blocked message when unverified claims exist |

## Database Entities

| Table | Key Fields |
|-------|------------|
| `truth_checks` | `id`, `claim_id`, `status` (confirmed/denied), `source`, `created_at` |
| `claims` | `id`, `session_id`, `category`, `status`, `content`, `verified_at` |
| `verification_requests` | `id`, `claimant_id`, `status`, `attempt_count`, `responded_at` |
| `verification_attempts` | `id`, `claimant_id`, `status`, `reason`, `drafting_status` |
| `cases` | `id`, `claimant_id`, `drafting_status` |
| `drafting_workflows` | `id`, `claim_id`, `status` (ready/on_hold), `reason` |

## Error Catalog

| Code | HTTP | Condition |
|------|------|-----------|
| `MINIMUM_SLOTS_NOT_MET` | 400 | Required slot count not satisfied |
| `TRUTH_CHECK_VALIDATION_ERROR` | 400 | Invalid claim_id, status, or source |
| `VERIFICATION_REQUEST_INVALID` | 400 | Missing/malformed claimantId |
| `CLAIMANT_NOT_FOUND` | 404 | No claimant record |
| `CLAIM_NOT_FOUND` | 404 | Disputed claim not in DB |
| `INVALID_STATE_TRANSITION` | 409 | State verifier rejected transition |
| `VERIFICATION_PERSISTENCE_FAILED` | 500 | DAO failure |
| `MALFORMED_WEBHOOK` | 400 | SMS dispute payload invalid |

---

*Source: TDD plans 296–297, 317–324 (session-1772314225364). All paths TLA+ verified.*
