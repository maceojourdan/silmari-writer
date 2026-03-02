# Specifications Index

Technical specifications for the CosmicHR Writer voice loop system.

## Architecture

| Document | Description |
|----------|-------------|
| [ARCHITECTURE.md](ARCHITECTURE.md) | System architecture: stack, diagrams, API surface, data model, integrations |

## Core Specification

| Document | Description |
|----------|-------------|
| [voice-loop.md](voice-loop.md) | Master spec: voice loop workflow, data model, state machine, LLM contracts, SMS spec, KPIs, UX screens |

## Domain Specifications

Consolidated from 47 TDD plans (paths 293–339). Each spec covers API endpoints, UI components, database entities, state transitions, validation schemas, and error catalogs.

| Document | Domain | Paths | Priority |
|----------|--------|-------|----------|
| [session-initialization.md](session-initialization.md) | Session creation, resume/job/question ingestion, consent | 293–295, 302, 310–312 | P0 |
| [voice-recall-story-selection.md](voice-recall-story-selection.md) | Orient phase, story selection, voice recall, slot prompting | 303–304, 306–309, 313–316 | P0 |
| [slot-filling-verification.md](slot-filling-verification.md) | Claim extraction, truth-check confirmation, verification pipeline | 296–297, 317–324 | P0 |
| [draft-generation-review.md](draft-generation-review.md) | Draft generation from claims, review workflow, approval | 298–300, 325–329 | P0 |
| [finalize-export-sms.md](finalize-export-sms.md) | Answer finalization, locking, export/copy, SMS follow-up | 305, 330–337 | P0 |
| [metrics-analytics.md](metrics-analytics.md) | Session metrics pipeline, leading KPIs, primary KPI tracking | 301, 338–339 | P0–P1 |

## Pipeline Specifications

| Document | Description |
|----------|-------------|
| [orchestration/file-to-llm-pipeline-model.md](orchestration/file-to-llm-pipeline-model.md) | File-attachment-to-LLM pipeline behavioral model (10 invariants) |
| [orchestration/file-to-llm-pipeline-target.md](orchestration/file-to-llm-pipeline-target.md) | Target spec for file-to-LLM pipeline |
| [orchestration/type-gating-pipeline-model.md](orchestration/type-gating-pipeline-model.md) | Type-gating pipeline behavioral model |
| [orchestration/type-gating-pipeline-target.md](orchestration/type-gating-pipeline-target.md) | Target spec for type-gating pipeline |

## Path Specifications

47 individual path specs in [orchestration/session-1772314225364/](orchestration/session-1772314225364/), each with:
- Resource reference table (UUID → implementation mapping)
- Step-by-step Input/Process/Output/Error definitions
- Terminal conditions
- TLA+ verification results (Reachability, TypeInvariant, ErrorConsistency)

## Schemas

| Document | Description |
|----------|-------------|
| [schemas/resource_registry.json](schemas/resource_registry.json) | Portable UUID registry mapping resources to implementations |

## Cross-References

### State Machine Phases → Spec Documents

| Phase | Primary Spec | Supporting Specs |
|-------|-------------|-----------------|
| INIT | session-initialization | voice-loop |
| ORIENT | voice-recall-story-selection | session-initialization |
| RECALL | voice-recall-story-selection, slot-filling-verification | voice-loop |
| VERIFY | slot-filling-verification | voice-loop |
| DRAFT | draft-generation-review | slot-filling-verification |
| REVIEW | draft-generation-review, finalize-export-sms | voice-loop |
| FINALIZE | finalize-export-sms | metrics-analytics |
| FOLLOWUP_SMS | finalize-export-sms | slot-filling-verification |

### LLM Roles → Spec Documents

| Role | Spec |
|------|------|
| LLM-A (Interviewer) | voice-recall-story-selection, voice-loop §5 |
| LLM-B (Coach) | voice-recall-story-selection, voice-loop §6 |
| LLM-C (Drafter) | draft-generation-review, voice-loop §8 |
