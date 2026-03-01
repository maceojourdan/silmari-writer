## CosmicHR Writer Voice Loop Spec (Job Seeker Side)

### Purpose

Enable candidates to produce **truthful, high-signal** application answers via **voice + SMS micro-loops**, by guiding memory recall and extracting concrete evidence that maps to job requirements and the application question.

### Primary KPI

* **Writer-assisted Application → Interview Conversion Rate**

### Leading KPIs (instrument immediately)

1. **Time-to-first-usable-draft** (seconds)
2. **Story completion rate** (% sessions where required slots filled)
3. **Truth-confirmation rate** (% key claims confirmed via Y/N)
4. **Signal density score** (count of concrete specifics per answer)
5. **Voice session drop-off rate** (% abandoned before draft)

---

# 1) Roles & Components

### Client

* Web/mobile UI with:

  * “Big record button”
  * Draft preview
  * One-tap approve/edit
  * Optional job link paste
  * Phone/SMS opt-in

### Voice Agent (ElevenLabs)

* Speaks prompts
* Streams audio + receives “next question” instructions
* Does not own long-term memory/state

### Backend Orchestrator (CosmicHR)

* Owns session state + schema
* Runs extraction, coaching, drafting
* Emits events to voice agent + SMS service

### Models (LLMs)

* **LLM-A Interviewer:** natural, supportive voice questioning
* **LLM-B Coach:** selects next best question based on missing slots/ambiguity
* **LLM-C Drafter:** produces final response using confirmed facts only

> Note: LLM-A can be the same model instance as LLM-C, but keep prompts distinct.

---

# 2) Data Model (Schema)

### Session

* `session_id`
* `user_id`
* `resume_object` (structured)
* `job_object` (structured)
* `question_object` (structured)
* `story_records[]`
* `transcript[]` (time-stamped turns)
* `draft_versions[]`
* `metrics` (timestamps, counters, scores)

### ResumeObject (minimum)

* `roles[]` {company, title, dates, bullets[], tools[], outcomes[]}
* `skills[]`
* `projects[]` (optional)
* `education[]`

### JobObject (minimum)

* `title`
* `company`
* `requirements_required[]`
* `requirements_preferred[]`
* `responsibilities[]`
* `keywords[]`
* `level` (junior/mid/senior)

### QuestionObject

* `question_text`
* `question_type` ∈ {behavioral_STAR, technical, leadership, conflict, motivation, culture, open_ended}
* `evaluation_targets[]` (what interviewer should elicit)

### StoryRecord (core)

* `story_id`
* `story_title` (user phrasing)
* `context` {role_title, company_context}
* `anchors` {when, where, stakes}
* `people[]` {role, relationship, responsibility}
* `objective`
* `constraints_obstacles[]`
* `actions[]` (ordered)
* `tools_tech[]`
* `outcomes` {metrics[], qualitative[]}
* `artifacts[]` (PR, ticket, dashboard, doc)
* `truth_checks[]` {claim, status ∈ {confirmed, denied, uncertain}, source_turn_id}
* `confidence` (0–1 user self-report)

---

# 3) Workflow Overview (State Machine)

### States

1. **INIT**: load resume/job/question
2. **ORIENT**: confirm what we’re answering + pick one story
3. **RECALL**: gather anchors + sequence + proof via voice
4. **VERIFY**: confirm key claims (voice or SMS)
5. **DRAFT**: generate structured answer
6. **REVIEW**: user approves/edits
7. **FOLLOWUP_SMS** (optional): micro-questions after session
8. **FINALIZE**: lock answer, export/copy, store structured data

### Transitions

* INIT → ORIENT automatically
* ORIENT → RECALL once story selected
* RECALL → VERIFY when minimum slots met
* VERIFY → DRAFT when key claims confirmed or marked uncertain
* DRAFT → REVIEW always
* REVIEW → FINALIZE if approved
* REVIEW → RECALL if user says “not accurate / missing”
* FINALIZE → FOLLOWUP_SMS if low confidence or missing optional slots

---

# 4) Minimum Slot Requirements (to draft)

### For Behavioral/STAR

Must have:

* objective
* actions (≥3 steps)
* outcome (≥1 metric OR 2 qualitative impacts)
* one obstacle
* role clarity (“what *you* did”)

### For Technical

Must have:

* problem statement
* environment (prod vs non-prod)
* approach (≥3 steps)
* tools_tech
* validation (how you knew it worked)
* outcome/impact

### For Motivation/Culture

Must have:

* reason aligned to job/company
* 1–2 specific examples from past
* values statement grounded in behavior

---

# 5) Interviewer (LLM-A) Prompt Contract

### Inputs

* `question_object`
* `job_object` key requirements
* `resume_object` highlights relevant to requirements
* `current_story_record`
* `missing_slots[]`
* `conversation_style` = “friendly, natural, concise, supportive”

### Output (strict JSON)

* `next_prompt_to_user` (one spoken question)
* `followup_if_no_memory` (one alternative)
* `slot_targeted` (which slot to fill)
* `expected_answer_type` ∈ {short, numeric, list, narrative}
* `stop_condition` (true/false) if RECALL can move to VERIFY

### Interviewer Question Style Rules

* One question at a time
* Use reflective listening (“So it sounds like…”)
* Ask for *concrete anchors* (when/where/team/tools)
* Never pressure; allow “skip”
* Avoid irrelevant personal descriptors (hair/clothes) unless user offers it; prefer role-based anchors

---

# 6) Coach (LLM-B) Prompt Contract

### Purpose

Given transcript + current slots, choose the **best next question** to increase signal density and alignment to job + question type.

### Inputs

* `question_type`
* `evaluation_targets`
* `missing_slots`
* `ambiguities[]` (e.g., vague claim, missing metric)
* `user_fatigue_score` (heuristic: time + turns)

### Output (strict JSON)

* `recommended_next_question`
* `why` (slot + alignment)
* `confidence` (0–1)
* `fallback_question`
* `fatigue_adjustment` (e.g., “make it yes/no”, “offer choices”)

---

# 7) Extractor (Deterministic + LLM optional)

Run after each user turn:

* Update StoryRecord slots via:

  * regex/heuristics for numbers, dates, tools
  * optional LLM extraction constrained to schema
* Produce:

  * `new_claims[]`
  * `key_claims_to_confirm[]` (metrics, scope, leadership, production)

### Claim Confirmation Rule

Any of these must be confirmed before final draft:

* metrics (“30%”, “$X”, “reduced time”)
* scope (“led team”, “owned architecture”)
* production environment claims
* security/compliance claims

---

# 8) Drafter (LLM-C) Output Format

### Inputs

* StoryRecord with truth_checks
* Job requirements + question
* Draft template for question_type

### Output

* `draft_text`
* `bullets_of_supporting_evidence[]` (for internal recruiter view)
* `claims_used[]` with status confirmed/uncertain
* `suggested_verification_sms[]` (max 3) if uncertain claims remain

### Drafting Rules

* Use only **confirmed** claims as hard facts
* If uncertain, either:

  * omit
  * phrase cautiously (“approximately”, “I estimate”)
* Keep answer length within common application limits (configurable)

---

# 9) SMS Micro-Loop Spec (Post-call)

### Trigger Conditions

* user ended session before VERIFY
* draft contains uncertain key claims
* confidence < 0.7
* missing metric/artifact but story otherwise good

### Message Types (one per SMS)

1. **Y/N Approval**

   * “Quick check: does this line sound accurate? ‘…’ Reply Y/N”
2. **Two-choice**

   * “Which is closer: saved hours/week (A) or days/month (B)?”
3. **Fill numeric**

   * “About how many people were on the project team? Reply with a number.”
4. **Artifact prompt**

   * “Was there a PR/ticket/doc you could point to? Reply PR / Ticket / Doc / None”

### Logging

Each reply updates `truth_checks` + relevant slot, with `source = sms`.

---

# 10) Events & Integration (Voice Agent ↔ Backend)

### Inbound from Voice Agent

* `AUDIO_CHUNK`
* `TRANSCRIPT_PARTIAL`
* `TRANSCRIPT_FINAL` {text, turn_id, timestamp}

### Backend emits to Voice Agent

* `SAY` {text}
* `HINTS` {tone, pacing, “keep short”}
* `STATE` {current_phase, progress_percent}

### Backend internal events

* `SLOTS_UPDATED`
* `COACH_NEXT_QUESTION_READY`
* `VERIFY_QUEUE_UPDATED`
* `DRAFT_READY`
* `USER_APPROVED`

---

# 11) Scoring (Signal Density)

Compute per draft:

* `num_metrics` (count of numeric claims)
* `num_specific_tools`
* `num_actions` (>=3 ideal)
* `num_artifacts`
* `alignment_hits` (mentions required skills/responsibilities)
* `vagueness_penalty` (heuristic: “helped”, “worked on”, “involved” without specifics)

Store:

* `signal_density_score = weighted_sum - penalty`

---

# 12) UX Screens (Minimal)

1. **Setup**

   * Upload resume
   * Paste job or job link
   * Paste question
2. **Voice Session**

   * Big record button
   * “Progress: Anchors / Actions / Outcomes”
3. **Draft Review**

   * Draft text
   * “Approve / Edit by voice”
4. **Confirmations**

   * Optional “Send me 3 quick texts to confirm details” toggle
5. **Export**

   * Copy / download

---

# 13) Compliance & Guardrails

* Explicit consent: “I’ll ask questions to help you remember details. Skip any.”
* Never fabricate facts
* Mark uncertain claims and confirm via voice/SMS
* Do not request sensitive personal info unrelated to work

---

## Acceptance Criteria (MVP)

* User can complete one question end-to-end (voice → draft → approve)
* System stores StoryRecord + truth checks
* Generates draft with confirmed claims only
* Sends optional SMS confirmations and updates the record
* Logs KPIs: time-to-draft, completion rate, confirmation rate, signal density

---
