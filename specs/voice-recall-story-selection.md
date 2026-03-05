# Voice Recall & Story Selection

**Domain:** Orient phase, story selection, voice recall, slot prompting, voice interaction
**Paths:** 303–304, 306–309, 313–316
**Priority:** P0

---

## Overview

After session initialization, the system guides the user through story selection (ORIENT) and voice-driven recall (RECALL). The user picks a story from their resume relevant to the question, then answers voice prompts to fill required slots (anchors, actions, outcomes). The Coach (LLM-B) selects optimal next questions based on missing slots and user fatigue.

## State Machine

```
ORIENT ──(story selected)──→ RECALL ──(minimum slots met)──→ VERIFY
  │                            ↑
  └─ story list rendered       └── re-prompt if slots incomplete
```

### ORIENT Sub-states
```
[Session in ORIENT] → Story list loaded → User selects story → Alignment verified → Story confirmed → RECALL
```

### RECALL Sub-states
```
[Prompt displayed] → Voice capture → Transcript extracted → Slots parsed → Missing slots re-evaluated
                                                                              ├─ still missing → next prompt
                                                                              └─ all met → VERIFY
```

### RECALL Question Advancement (Three-Actor Sync)

Three actors hold independent copies of `questionProgress`:

| Actor | State Location | Updated When |
|-------|---------------|-------------|
| UI (React) | `questionProgress` state in RecallScreen | Immediately on button click |
| Backend (DB) | `question_progress` JSONB in story_records | Via `POST /api/session/voice-turns` action=advance_question |
| LLM (Realtime) | `instructions` parameter in voice session | Via `session.update` sent over data channel on advance |

**Advancement paths:**
- **Move-on intent** (voice stays connected): `detectMoveOnIntent` → stop controls shown → "Next question" button → `advanceQuestionFlow` → UI advances + backend persists + LLM instructions synced via `sendEvent({ type: 'session.update' })`
- **Manual stop** (voice disconnects): Stop button → disconnect → stop controls → "Next question" → advance UI + backend → next Record reconnects with fresh instructions

**Invariant:** While voice session is connected, `uiIndex == llmIndex` must hold. See [question-desync-model.md](orchestration/question-desync-model.md) for TLA+ verification.

### RECALL Source-Aware Persistence
- `sessionSource='answer_session'`:
  - final transcript persists through `/api/session/voice-response`
  - working answer and question progress persist through `/api/session/voice-turns`
- `sessionSource='session'`:
  - final transcript skips `/api/session/voice-response`
  - persistence uses `/api/session/voice-turns` only
- missing `sessionSource`: fail-closed behavior, no transcript submit.

### Canonical Session Resolver
All story record lookups use `SessionDAO.findStoryRecordByCanonicalSessionId(sessionId, preferredSource)` which implements a fallback chain:
1. Try preferred column (`voice_session_id` for `answer_session`, `session_id` for `session`)
2. If null, try the alternate column

This eliminates the split-brain mismatch where `sessionSource="session"` failed to find records linked only via `voice_session_id`. See [recall-advancement-model.md](orchestration/recall-advancement-model.md) for TLA+ verification.

## API Endpoints

| Method | Path | Request | Response |
|--------|------|---------|----------|
| `POST` | `/api/orient/story` | `OrientEventSchema` | Story record created |
| `GET` | `/api/story/orient-context` | `?questionId=...` | `{ question, jobRequirements, stories }` |
| `POST` | `/api/story/confirm` | `ConfirmStoryRequestSchema` | Confirmation result |
| `POST` | `/api/session/voice-response` | Voice transcript payload | Processed voice response |
| `GET` | `/api/session/voice-turns` | `?sessionId=...&sessionSource=answer_session|session` | `{ sessionId, sessionSource, workingAnswer, turns, questionProgress }` |
| `POST` | `/api/session/voice-turns` | `{ sessionId, sessionSource, action, ... }` | `{ sessionId, sessionSource, workingAnswer, turns, questionProgress }` |
| `POST` | `/api/session/submit-slots` | `{ sessionId, questionType, slotValues, attemptCount }` | `{ prompts, attemptCount, guidanceHint? }` |

## UI Components

| Component | Props | Purpose |
|-----------|-------|---------|
| `StorySelection` | `stories[], questionId, jobId?` | Radio-button story picker with alignment verification |
| `StorySelectionList` | `stories[], onSelectionChange?` | Story list with per-item error boundaries |
| `StorySelectionConfirm` | `selectedStoryIds[], onConfirmed?` | Validates single selection, calls confirm API |
| `RecallScreen` | `progress?, sessionId?, sessionSource?, questions?, initialQuestionProgress?` | Voice recall with question progression, LLM coaching, working answer persistence |
| `RecallLayout` | `progress, forceError?` | RecallScreen wrapper with error boundary |
| `RecordButton` | `prominent?, disabled?` | Large red record button (w-32 h-32) |
| `ProgressIndicator` | `progress: { anchors, actions, outcomes }` | Three labeled numeric values |
| `RecallSlotPrompt` | `sessionId, questionType, prompts, attemptCount` | Slot submission form with guidance hints |
| `VoiceInteraction` | `payload: NextStepPayload` | Web Speech API TTS for prompts |
| `VoiceSessionComponent` | `session, onSessionProgressed?` | Voice transcript submission |

## Database Entities

| Table | Key Fields |
|-------|------------|
| `stories` | `id`, `session_id`, `story_title`, `context`, `anchors`, `people[]`, `objective` |
| `story_records` | Full StoryRecord schema (see voice-loop.md §2) |

Legacy prep-session durability notes:
- For `sessionSource='session'`, first working-answer write creates a prep-linked `story_records.session_id` row if missing.
- If Supabase schema cache is stale for `question_progress`, creation retries without that column to preserve durable save behavior.

## LLM Contracts

### Coach (LLM-B) — Question Selection

**Inputs:** `question_type`, `evaluation_targets`, `missing_slots`, `ambiguities[]`, `user_fatigue_score`

**Output (strict JSON):**
```ts
{
  recommended_next_question: string;
  why: string;           // slot + alignment reasoning
  confidence: number;    // 0–1
  fallback_question: string;
  fatigue_adjustment: string; // e.g. "make it yes/no"
}
```

### Interviewer (LLM-A) — Voice Prompting

**Output (strict JSON):**
```ts
{
  next_prompt_to_user: string;
  followup_if_no_memory: string;
  slot_targeted: string;
  expected_answer_type: 'short' | 'numeric' | 'list' | 'narrative';
  stop_condition: boolean;
}
```

## Error Catalog

| Code | HTTP | Condition |
|------|------|-----------|
| `ORIENT_ERROR` | 500 | Story record creation failure |
| `CONFIRM_STORY_ERROR` | 500 | Story confirmation failure |
| `SLOT_SUBMISSION_INVALID` | 400 | Malformed slot payload |
| `WORKFLOW_GUARD_VIOLATION` | 409 | Zero newly satisfied slots |
| `VOICE_RECOGNITION_ERROR` | — | Transcript empty or recognition failure |
| `SLOT_PARSING_ERROR` | — | No recognizable slots in utterance |
| `UNAUTHORIZED` | 401 | Missing/invalid auth on `/api/session/voice-response` |
| `INVALID_STATE` | 409 | Owned prep/session ID sent to `/api/session/voice-response` |
| `SESSION_NOT_FOUND` | 404 | Missing/unauthorized ID in `/api/session/voice-response` |

---

*Source: TDD plans 303–304, 306–309, 313–316 (session-1772314225364). All paths TLA+ verified.*
