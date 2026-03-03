# Voice-Assisted Session UI/UX

## Why this exists
Job application questions are similar, but not similar enough. Most candidates feel like they have to restart from scratch each time.

This UI/UX is designed to remove that friction by guiding the user through a voice-assisted interrogation flow that pulls the right details from their real experience and turns them into stronger answers.

## UX north star
- `Great experience` for the job seeker means: `Confidence`.
- The interaction model during voice interrogation is: `Iterative refinement`.

## Product promise to the user
- "You do not have to write from a blank page."
- "We help you find the strongest version of your real story."
- "We avoid generic AI slop by grounding every draft in your verified details."

## End-to-end UI journey

### 1. Onboarding first (candidate context)
Before ingestion and voice interrogation, the user completes a quick onboarding step so the system has enough context to provide tailored guidance.

Onboarding inputs:
1. Upload resume file.
2. Paste LinkedIn profile URL.
3. Optionally enter LinkedIn profile details manually if URL parsing fails.
4. Optionally connect LinkedIn account through an explicit OAuth-style connect flow.

Onboarding outputs:
1. Candidate profile baseline (experience themes, strengths, domain areas).
2. Reusable story seeds for later voice sessions.
3. Suggested contribution themes that can be mapped to target companies.

### 2. Ingestion (make it convenient)
After onboarding, the user can provide the target application context in any of these ways:

1. Paste a URL directly in the app.
2. Send the URL by email to a system-provided inbox address.
3. Send the URL by SMS/text to a system-provided number.

The system ingests the URL and extracts relevant context (question prompts, role expectations, and related signals) so the user does not need to manually copy everything.

### 3. Entry and orientation
The user starts a voice-assisted session, sees the detected question context, and confirms the story they want to use.

The system prevents weak starts by blocking:
- no story selected
- multiple stories selected
- misaligned story selection

### 4. Voice interrogation loop (iterative refinement)
The core interaction loop:

1. User speaks.
2. System transcribes and reflects back.
3. System asks targeted follow-up questions for missing details.
4. User adds more detail.
5. Loop repeats until required slots are complete.

The user should always see:
- current transcript
- what is still missing
- progress through the loop

### 5. Verification and draft generation
Claims that matter (metrics, scope, production impact, security context) are verified before drafting.

Drafts are generated from confirmed claims only. Unverified or incomplete claims are excluded, with clear messaging.

### 6. Review, voice edits, and finalize
User can approve, edit by voice, or return to recall. Finalize locks the answer. Export/copy is available after lock.

### 7. Job-search acceleration layer (short list + network + content)
Outside any single question, the system helps the candidate run a focused job-search strategy:

1. Build a short list of companies to learn about.
2. For each short-list company, identify likely contribution areas based on candidate background and company context.
3. Help the candidate find relevant people at each short-list company (hiring managers, peers, recruiters, adjacent teams).
4. Generate tailored outreach drafts and talking points for those contacts.
5. Generate LinkedIn post drafts mapped to the same contribution areas and company themes.

LinkedIn policy guardrail:
- The software does not post on the user's behalf.
- The software prepares draft content and the user manually posts it.

Copy-first UX rule:
- Every completed text artifact must expose a conspicuous `Copy` button.
- This includes outreach drafts, LinkedIn post drafts, application answers, and summary notes.
- Copy action should provide immediate visual confirmation that text is in clipboard.

## Interstitial steps to reduce "blocked" feeling
To prevent users from feeling stalled while the system processes, the UI must include short static interstitial overlays between major stages.

These overlays should:
- explain what is happening now
- explain why this step improves interview outcomes
- reinforce that the process is building a truthful, high-signal answer (not AI slop)

### Interstitial examples
1. `After ingestion starts`
   - "We are reading the application context so you do not need to rewrite your story from scratch."
2. `Before voice recall`
   - "Strong interview answers combine clear actions, measurable impact, and context. We will guide you to all three."
3. `Before verification/draft`
   - "We only draft from confirmed details to avoid generic AI language and protect credibility."

### Interstitial UX rules
1. Keep overlays short, calm, and confidence-building.
2. Never present them as error states.
3. Always show visible forward motion (step name + progress indicator).
4. Provide a clear continue/wait affordance.

## Confidence criteria (what "great" means in practice)
The user should leave each session feeling:
1. "My answer sounds like me."
2. "My evidence is stronger than what I would have written alone."
3. "I understand why the system asked these follow-ups."
4. "I can trust this in an interview."

## Observability and KPI framework
We need KPI instrumentation that connects product usage to business outcomes, not just button clicks.

### KPI hierarchy (consulting-style)
1. `North Star Outcome`
   - Application-to-interview conversion rate uplift for users who complete the voice-assisted flow.
2. `Primary Business Outcomes`
   - Interview-to-offer conversion uplift.
   - Repeat usage rate across multiple applications per user.
3. `Experience Outcomes`
   - Confidence score uplift (pre-session vs post-session self-rating).
   - "Blocked feeling" reduction score (post-step pulse check).
4. `Process and Quality Drivers`
   - Time to first usable draft.
   - Claim verification pass rate.
   - Confirmed-claim inclusion rate in final draft.
   - AI slop avoidance score (generic-language flags per answer).
5. `Operational Health`
   - Voice/session reliability and latency SLOs.
   - Ingestion success rates by channel (paste, email, SMS).

### KPI definitions that must be measurable
1. `Application-to-interview conversion uplift`
   - Formula: `(interview_rate_voice_flow - interview_rate_control) / interview_rate_control`
2. `Confidence uplift`
   - Formula: `avg(post_session_confidence - pre_session_confidence)`
3. `Perceived blocked rate`
   - Formula: `sessions_with_blocked_feedback / total_sessions`
4. `Rewrite reduction`
   - Formula: `avg(self_reported_manual_rewrites_per_application)` trend down over time
5. `Draft quality integrity`
   - Formula: `confirmed_claims_used / total_claims_used`
6. `Ingestion convenience success`
   - Formula: `successful_ingestions / ingestion_attempts` by each channel

### Stage funnel and drop-off telemetry
Track conversion and dwell between each stage:
1. `ONBOARDING_COMPLETED`
2. `INGESTED`
3. `SESSION_STARTED`
4. `ORIENT_CONFIRMED`
5. `RECALL_COMPLETED`
6. `VERIFICATION_PASSED`
7. `DRAFT_GENERATED`
8. `REVIEW_APPROVED`
9. `FINALIZED`
10. `EXPORTED_OR_COPIED`

For each transition capture:
- transition success/failure
- time spent in prior stage
- retries/attempt count
- explicit failure reason code

### Ingestion observability requirements
For URL ingestion, instrument channel-specific events:
1. `ingestion_url_submitted` (channel=`paste|email|sms`)
2. `ingestion_parse_succeeded`
3. `ingestion_parse_failed`
4. `ingestion_context_ready`

Minimum fields:
- `session_id`
- `user_id`
- `channel`
- `source_domain`
- `time_to_context_ready_ms`
- `error_code` (if failed)

### Onboarding observability requirements
Instrument onboarding completion and profile quality:
1. `resume_upload_started`
2. `resume_upload_succeeded`
3. `linkedin_url_submitted`
4. `linkedin_profile_parsed`
5. `linkedin_connect_started`
6. `linkedin_connect_completed`
7. `onboarding_completed`

Minimum fields:
- `session_id`
- `user_id`
- `resume_parse_status`
- `linkedin_input_mode` (`url|manual|connected`)
- `onboarding_time_ms`
- `error_code` (if failed)

### Short-list and network observability requirements
Instrument candidate activation beyond answer writing:
1. `shortlist_generated`
2. `shortlist_company_saved`
3. `company_contribution_area_generated`
4. `company_contacts_suggested`
5. `outreach_draft_generated`
6. `linkedin_post_draft_generated`
7. `artifact_copied_to_clipboard`

Minimum fields:
- `session_id`
- `user_id`
- `company_id_or_name`
- `artifact_type` (`answer|outreach|linkedin_post|summary`)
- `copy_success`
- `time_to_artifact_ms`

### Interstitial observability requirements
Because interstitials are intended to reduce blocked feelings, track:
1. `interstitial_shown`
2. `interstitial_dismissed_or_continued`
3. `interstitial_abandonment` (user exits during overlay)

Minimum fields:
- `interstitial_type`
- `step_before`
- `step_after`
- `dwell_ms`
- `cta_action`

### New-Path Telemetry Ingestion Contract (Required)
To ensure the above observability requirements are enforceable in production, telemetry emission must have an explicit server ingress contract.

Required endpoint:
1. `POST /api/telemetry/new-path-events`

Required request shape:
1. Top-level envelope:
   - `event_name` (string enum matching supported new-path events)
   - `payload` (event-specific object validated against event schema)
2. For interstitial events, `payload` must include the fields listed in Interstitial observability requirements.

Required behavior:
1. Route validates `event_name` + `payload` against typed event schemas.
2. Route delegates persistence/routing through shared telemetry gateway.
3. Telemetry failures are non-blocking for UX flows:
   - return accepted response semantics even when downstream sink write fails
   - log failure with structured error metadata.
4. Route must support browser telemetry delivery patterns (`POST`, and `OPTIONS` for preflight-safe behavior).
5. Unsupported methods should return explicit method errors (`405`) with allowed methods declared.

### Voice interrogation observability requirements
Track iterative refinement quality:
1. `voice_turn_started` / `voice_turn_completed`
2. `transcript_final_received`
3. `slot_missing_prompted`
4. `slot_filled`
5. `slot_reprompted`
6. `recall_loop_completed`

Minimum fields:
- `question_type`
- `attempt_count`
- `slots_required`
- `slots_filled`
- `missing_slot_keys`
- `turn_latency_ms`

### Verification and anti-AI-slop observability
1. `claim_verification_requested`
2. `claim_verified`
3. `claim_disputed`
4. `draft_generated_with_confirmed_claims_only`
5. `draft_omission_notice_shown`

Minimum fields:
- `claim_type`
- `verification_channel`
- `verification_status`
- `claims_included_count`
- `claims_omitted_count`
- `omission_reason_codes`

### Operational SLO monitoring
Track and alert on:
1. API p95/p99 latency by endpoint (`/api/sessions`, `/api/story/*`, `/api/session/*`, `/api/draft/*`)
2. Voice session startup failure rate
3. Transcript failure rate
4. Verification timeout rate
5. Finalization failure rate

### Dashboard cadence
1. `Daily ops dashboard`
   - Reliability, latency, failures, current drop-off spikes.
2. `Weekly product dashboard`
   - Funnel conversion, blocked-rate trends, confidence uplift, ingestion channel performance.
3. `Monthly strategy dashboard`
   - Interview conversion uplift, offer conversion uplift, retention/repeat usage, ROI narrative.

### Decision thresholds (example guardrails)
1. If `perceived_blocked_rate > 15%` for two consecutive weeks, prioritize interstitial/content redesign.
2. If `ingestion_success_rate < 95%` on any channel, treat as P0 reliability issue.
3. If `confirmed_claims_used / total_claims_used < 0.9`, block broad rollout until fixed.
4. If `confidence_uplift` is flat for 4 weeks, revisit prompt strategy and recall UX.
5. If `onboarding_completion_rate < 85%`, simplify onboarding inputs and reduce friction.
6. If `artifact_copied_to_clipboard` usage is low, improve Copy button prominence and placement.

## Non-negotiable requirements
1. Onboarding supports resume upload plus LinkedIn input (URL, manual fallback, optional account connect).
2. URL ingestion supports paste, email, and SMS entry paths.
3. Voice interrogation uses iterative refinement, not one-shot capture.
4. Interstitial overlays exist at key transition points to reduce perceived blocking.
5. Messaging explicitly differentiates this process from generic AI-generated output.
6. System supports short-list company research, contact discovery guidance, contribution-area discovery, and LinkedIn content drafting.
7. Software does not auto-post to LinkedIn on the user's behalf.
8. Every completed text output has a conspicuous `Copy` button for clipboard copy.
9. UI language optimizes for candidate confidence from start to finalize.
10. KPI instrumentation is implemented end-to-end across onboarding, ingestion, interstitials, voice loop, verification, draft, finalize, and copy actions.

## Orchestration traceability references
The following references map this UI/UX spec to `specs/orchestration/session-1772314225364`.

### Covered by existing orchestration paths
1. `Onboarding baseline inputs and session initialization`
   - Applies: `294`, `310`, `311`, `312`
   - Why: Covers resume/job/question object intake, initialization, duplicate prevention, and invalid-object rejection.
2. `Entry, consent, and ORIENT story confirmation`
   - Applies: `302`, `306`, `295`, `313`, `314`, `315`, `316`
   - Why: Covers affirmative consent, session start, story record setup, and single aligned story confirmation.
3. `Voice interrogation (iterative refinement)`
   - Applies: `303`, `304`, `307`, `317`, `318`, `319`, `320`, `296`
   - Why: Covers record/progress UI, SAY/transcript behavior, voice processing, missing-slot reprompts, and transition to VERIFY after minimum slots.
4. `Verification and claim truth controls`
   - Applies: `297`, `321`, `322`, `323`, `324`, `305`
   - Why: Covers claim confirmation, voice/SMS verification, disputes, missing-contact failure, timeout behavior, and uncertain-claim SMS follow-up.
5. `Draft/review/finalize/export/immutability`
   - Applies: `298`, `299`, `300`, `325`, `326`, `327`, `328`, `329`, `330`, `331`, `332`, `333`, `334`, `335`, `336`, `337`, `308`, `309`, `293`
   - Why: Covers confirmed-claim-only draft generation, review approval, voice edit behavior, finalize lock, export/copy, SMS follow-up variants, and finalized-state immutability.
6. `Analytics and KPI eventing baseline`
   - Applies: `301`, `338`, `339`, `300`
   - Why: Covers session metrics persistence and leading/primary KPI event recording.

### Partially covered (now resolved)
1. `Ingestion convenience (URL paste/email/SMS)`
   - Original gap: explicit email-to-ingest and SMS-to-ingest ingestion channel flows were not specified.
   - Now covered by: `340` (ingest-url-via-email-or-sms-channel)
2. `Conspicuous Copy actions on completed artifacts`
   - Original gap: copy requirements for artifact types beyond finalized answers were not specified.
   - Now covered by: `341` (copy-artifact-to-clipboard)

### Previously not covered (now resolved)
1. LinkedIn onboarding and optional LinkedIn account connect flow.
   - Now covered by: `342` (linkedin-onboarding-connect-flow)
2. Company short-list generation and management.
3. Contact discovery guidance for each short-list company.
4. Contribution-area discovery per company.
   - Items 2-4 now covered by: `343` (shortlist-contacts-contribution-discovery)
5. LinkedIn content planning workflow tied to short-list companies.
6. Explicit "manual post only" safeguards and UX checks for LinkedIn policy compliance.
   - Items 5-6 now covered by: `344` (linkedin-content-planning-workflow)
7. Interstitial overlay content/UX rules and anti-blocking treatment as a first-class orchestration flow.
   - Now covered by: `345` (interstitial-overlay-orchestration)
