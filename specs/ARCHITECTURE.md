# CosmicHR Writer — System Architecture

## System Overview

CosmicHR Writer is an AI-powered voice interview system that helps job seekers produce truthful, high-signal application answers. Candidates speak through a structured voice loop, and the system extracts concrete evidence, verifies claims, and generates polished drafts.

**Primary KPI:** Writer-assisted Application → Interview Conversion Rate

## Technology Stack

| Layer | Technology |
|-------|-----------|
| Framework | Next.js 16 (App Router) + React 19 + TypeScript 5 |
| Styling | Tailwind CSS 4 |
| State Management | Zustand 5 (localStorage persistence) |
| Validation | Zod 4 |
| Database | Supabase (PostgreSQL) — stubs, not yet wired |
| LLM Framework | BAML (Boundary ML) |
| LLM Providers | OpenAI (GPT-5, GPT-5-mini), Anthropic (Claude Opus 4.1, Sonnet 4) |
| Voice | ElevenLabs (TTS), OpenAI Realtime API (WebRTC), Web Speech API |
| SMS | Twilio |
| Storage | Vercel Blob |
| Testing | Vitest + React Testing Library + Playwright |
| Deployment | Vercel (sfo1 region) |

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                          Browser (React 19)                         │
│                                                                     │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────────┐   │
│  │  Zustand  │  │   Chat   │  │  Voice   │  │  Domain Workflow │   │
│  │  Store    │  │   UI     │  │  Panel   │  │  Components      │   │
│  └──────────┘  └──────────┘  └──────────┘  └──────────────────┘   │
│       │              │             │                │               │
│  ┌────┴──────────────┴─────────────┴────────────────┴────────┐     │
│  │              Frontend Verifiers (Zod)                      │     │
│  │              API Contracts (typed fetch)                    │     │
│  └────────────────────────────┬───────────────────────────────┘     │
└───────────────────────────────┼─────────────────────────────────────┘
                                │ HTTP
┌───────────────────────────────┼─────────────────────────────────────┐
│                    Next.js API Routes (42 endpoints)                │
│                                                                     │
│  ┌──────────┐  ┌──────────────┐  ┌──────────────┐  ┌───────────┐  │
│  │  Filters │→ │   Request    │→ │  Services /   │→ │   DAOs    │  │
│  │  (Auth)  │  │   Handlers   │  │  Processors   │  │  (Stubs)  │  │
│  └──────────┘  └──────────────┘  └──────────────┘  └───────────┘  │
│       │              │                  │                │          │
│  ┌────┴──────────────┴──────────────────┴────────────────┴───┐     │
│  │           Server Verifiers (Zod) + Error Definitions       │     │
│  │           Data Structures (Zod schemas + TS interfaces)    │     │
│  └────────────────────────────────────────────────────────────┘     │
└────────────────────────────────┬────────────────────────────────────┘
                                 │
        ┌────────────┬───────────┼───────────┬────────────┐
        ▼            ▼           ▼           ▼            ▼
   ┌─────────┐ ┌──────────┐ ┌────────┐ ┌─────────┐ ┌──────────┐
   │Supabase │ │ OpenAI   │ │ BAML   │ │ Twilio  │ │ Vercel   │
   │ (stub)  │ │ APIs     │ │ LLMs   │ │  SMS    │ │  Blob    │
   └─────────┘ └──────────┘ └────────┘ └─────────┘ └──────────┘
```

## Voice Loop State Machine

```
┌──────┐     ┌────────┐     ┌────────┐     ┌────────┐     ┌───────┐
│ INIT │────→│ ORIENT │────→│ RECALL │────→│ VERIFY │────→│ DRAFT │
└──────┘     └────────┘     └────────┘     └────────┘     └───────┘
                              ↑    │                          │
                              │    │ (min slots met)          │
                              │    ▼                          ▼
                              │  re-prompt              ┌────────┐
                              │                         │ REVIEW │
                              │                         └────────┘
                              │                           │    │
                              └───("not accurate")────────┘    │
                                                               ▼
                                                         ┌──────────┐
                                                         │ FINALIZE │
                                                         └──────────┘
                                                               │
                                                               ▼
                                                        ┌─────────────┐
                                                        │FOLLOWUP_SMS │
                                                        │ (optional)  │
                                                        └─────────────┘
```

### State Descriptions

| State | Description | Exit Condition |
|-------|-------------|----------------|
| INIT | Load resume, job posting, question | Automatic → ORIENT |
| ORIENT | Confirm question, select story from resume | Story selected → RECALL |
| RECALL | Voice-driven slot filling (anchors, actions, outcomes) | Minimum slots met → VERIFY |
| VERIFY | Confirm key claims (metrics, scope, production, security) | All claims resolved → DRAFT |
| DRAFT | LLM-C generates answer using confirmed claims only | Always → REVIEW |
| REVIEW | User approves or requests edits | Approved → FINALIZE |
| FINALIZE | Lock answer, export, store structured data | Complete |
| FOLLOWUP_SMS | Post-session SMS verification of uncertain claims | Async |

## Server-Side Architecture

### Layered Request Flow

```
Route Handler (app/api/*)
  │
  ├─→ AuthAndValidationFilter (JWT stub + Zod body validation)
  │
  ├─→ Request Handler (stateless, maps DTO → command)
  │     │
  │     ├─→ Service (domain logic, orchestration)
  │     │     │
  │     │     ├─→ Processor (business rules, transformations)
  │     │     │     │
  │     │     │     └─→ Process Chain (multi-step orchestration)
  │     │     │
  │     │     ├─→ Verifier (Zod schema validation)
  │     │     │
  │     │     └─→ DAO (Supabase stubs)
  │     │
  │     └─→ Transformer (data shape conversion)
  │
  └─→ Error Definition (typed error → HTTP response)
```

### Directory Structure

```
frontend/src/
├── app/api/                    # 42 API route handlers
├── components/                 # 90 React components
├── modules/                    # 10 feature modules (41 files)
├── hooks/                      # Custom React hooks
├── lib/                        # Utilities, store, types
├── verifiers/                  # 31 frontend validators
├── api_contracts/              # 23 typed API client functions
├── access_controls/            # Route guards
├── data_loaders/               # Async data fetching
├── logging/                    # Client-side logging
├── server/
│   ├── request_handlers/       # 53 handler classes
│   ├── services/               # 35 domain services
│   ├── processors/             # 19 processors
│   ├── process_chains/         # 25 multi-step chains
│   ├── transformers/           # 9 data transformers
│   ├── verifiers/              # 37 server validators
│   ├── filters/                # Auth filter
│   ├── data_access_objects/    # 34 DAO stubs
│   ├── data_structures/        # 36 Zod schemas + interfaces
│   ├── error_definitions/      # 35 error classes
│   └── logging/                # 14 structured loggers
└── baml_src/                   # BAML LLM definitions
```

## API Surface

### Session & Workflow (11 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| POST | `/api/sessions` | Create session |
| POST | `/api/sessions/initialize` | Full init (resume + job + question) |
| POST | `/api/sessions/[id]/approve` | Approve session |
| POST | `/api/sessions/[id]/finalize` | Finalize session |
| POST | `/api/session/init` | Legacy session init |
| POST | `/api/session/submit-slots` | Submit recall slots |
| POST | `/api/session/voice-response` | Process voice response |
| POST | `/api/orient/story` | Create story record |
| GET | `/api/story/orient-context` | Get orient context |
| POST | `/api/story/confirm` | Confirm story selection |
| POST | `/api/approve-story` | Approve story draft |

### Draft & Review (5 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| POST | `/api/generate-draft` | Generate from claim set |
| POST | `/api/draft/generate` | Generate (case/story/session) |
| POST | `/api/finalize` | Finalize draft workflow |
| POST | `/api/review/approve` | Approve content in review |
| POST | `/api/edit-by-voice` | Voice-driven content edit |

### Answer Management (3 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| PUT | `/api/answers/[id]` | Update answer content |
| POST | `/api/answers/[id]/finalize` | Finalize and lock answer |
| GET | `/api/answers/[id]/export` | Export (markdown/plain text) |

### Verification & Claims (5 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| POST | `/api/behavioral-question/evaluate` | Evaluate slot completeness |
| POST | `/api/truth-checks/confirm` | Confirm/deny claim |
| POST | `/api/verification/initiate` | Start verification flow |
| GET | `/api/claims/[claimId]/status` | Get claim status |
| GET | `/api/case/[caseId]/state` | Get case drafting state |

### SMS & Webhooks (2 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| POST | `/api/sms/webhook` | Twilio inbound SMS |
| POST | `/api/sms/dispute` | SMS dispute handling |

### Voice & Audio (5 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| POST | `/api/voice/session` | WebRTC SDP exchange |
| POST | `/api/voice/edit` | Voice-driven message edit |
| POST | `/api/voice-session/start` | Consent-gated voice start |
| POST | `/api/transcribe` | Whisper audio transcription |
| POST | `/api/upload` | Vercel Blob file upload |

### Analytics & KPI (3 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| POST | `/api/analytics` | Client telemetry events |
| POST | `/api/kpi/primary` | Record primary KPI |
| POST | `/api/onboarding/complete` | Complete onboarding step |

### AI Tools (5 endpoints)
| Method | Path | Purpose |
|--------|------|---------|
| POST | `/api/generate` | Chat completion (GPT-4o-mini) |
| POST | `/api/tools/deep-research` | Deep research |
| GET | `/api/tools/deep-research/[id]/status` | Poll research status |
| GET | `/api/tools/deep-research/[id]/stream` | SSE research stream |
| POST | `/api/tools/intent-classification` | Intent classification |
| POST | `/api/tools/document-generation` | PDF/DOCX/XLSX generation |
| POST | `/api/tools/image-generation` | Image generation |

## Data Model

### Core Entities

```
sessions ─────────┐
  │                │
  ├─ resume_object │
  ├─ job_object    │
  ├─ question_object│
  │                │
  ├─→ stories ─────┤
  │     │          │
  │     └─→ story_records
  │           │
  │           ├─→ truth_checks (claim, status, source)
  │           ├─→ draft_versions
  │           └─→ story_metrics
  │
  ├─→ behavioral_questions
  │
  ├─→ claims ──────→ verification_requests
  │     │                   │
  │     │                   └─→ delivery_attempts
  │     │
  │     └──→ cases ──→ drafting_workflows
  │
  ├─→ drafts ──→ answers (finalized, locked)
  │
  ├─→ session_metrics
  │
  └─→ events (category, timestamp, metadata)

users
  ├─→ sms_follow_ups
  └─→ onboarding

analytics_events (leading KPI)
primary_kpi_events (primary KPI)
```

### Key Enums

| Entity | Status Values |
|--------|--------------|
| Session | INIT, IN_PROGRESS, RECALL, COMPLETE, VERIFY, DRAFT, FINALIZE |
| Answer | DRAFT, COMPLETED, FINALIZED |
| Claim | UNCERTAIN, CONFIRMED, DENIED, PENDING, UNVERIFIED |
| Claim (verified) | unverified, verified, not_verified |
| Verification | pending, confirmed, failed, timed_out |
| Draft | DRAFT, APPROVED, FINALIZED |
| Content | DRAFT, REVIEW, APPROVED, FINALIZE |
| Drafting | allowed, blocked_due_to_unverified_claims |

## LLM Architecture

### Three LLM Roles

| Role | Purpose | Provider |
|------|---------|----------|
| LLM-A (Interviewer) | Natural voice questioning, reflective listening | BAML (GPT-5 / Claude) |
| LLM-B (Coach) | Select optimal next question based on missing slots + fatigue | BAML (GPT-5 / Claude) |
| LLM-C (Drafter) | Generate final answer from confirmed claims only | BAML (GPT-5 / Claude) |

### BAML Client Configuration

```
CustomGPT5        → openai-responses/gpt-5 (retry: exponential, max 3)
CustomGPT5Mini    → openai-responses/gpt-5-mini
CustomOpus4       → anthropic/claude-opus-4-1-20250805
CustomSonnet4     → anthropic/claude-sonnet-4-20250514
CustomHaiku       → anthropic/claude-3-5-haiku-20241022
CustomFast        → round-robin(GPT5Mini, Haiku)
OpenaiFallback    → fallback(GPT5Mini, GPT5)
```

## External Integrations

```
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│   OpenAI     │     │  Anthropic   │     │  ElevenLabs  │
│              │     │              │     │              │
│ • GPT-5      │     │ • Opus 4.1   │     │ • TTS        │
│ • Whisper-1  │     │ • Sonnet 4   │     │              │
│ • Realtime   │     │ • Haiku      │     │              │
│ • DALL-E     │     │              │     │              │
└──────────────┘     └──────────────┘     └──────────────┘

┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│   Twilio     │     │   Supabase   │     │ Vercel Blob  │
│              │     │              │     │              │
│ • SMS send   │     │ • PostgreSQL │     │ • Audio      │
│ • Webhooks   │     │ • Auth (TBD) │     │ • Files      │
│              │     │ • Realtime   │     │              │
└──────────────┘     └──────────────┘     └──────────────┘
```

## Validation Architecture

Three-layer validation at every boundary:

```
Layer 1: Route Handler     → Zod.safeParse(rawBody) → 400 on failure
Layer 2: Frontend Verifier → Zod.safeParse(input)   → blocks API call
Layer 3: API Contract      → Zod.safeParse(response) → throws on malformed
```

35 error definition classes ensure typed error propagation with `{ code, message, statusCode }`.

## Testing Strategy

| Type | Count | Framework | Pattern |
|------|-------|-----------|---------|
| Unit | 330+ | Vitest | Co-located `__tests__/` dirs |
| Integration | 45+ | Vitest | `*.integration.test.ts` |
| E2E | TBD | Playwright | `e2e/` directory |

All 47 path specs have TLA+ formal verification (Reachability, TypeInvariant, ErrorConsistency).

## Current Status

- All DAOs are stubs (not wired to Supabase)
- Auth is stub (presence-only, no JWT verification)
- 700+ source files, 330+ test files
- 47 TDD plans implemented with TLA+ verification
- Production deployment pending Supabase wiring
