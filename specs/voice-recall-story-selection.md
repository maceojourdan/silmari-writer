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

## API Endpoints

| Method | Path | Request | Response |
|--------|------|---------|----------|
| `POST` | `/api/orient/story` | `OrientEventSchema` | Story record created |
| `GET` | `/api/story/orient-context` | `?questionId=...` | `{ question, jobRequirements, stories }` |
| `POST` | `/api/story/confirm` | `ConfirmStoryRequestSchema` | Confirmation result |
| `POST` | `/api/session/voice-response` | Voice transcript payload | Processed voice response |
| `POST` | `/api/session/submit-slots` | `{ sessionId, questionType, slotValues, attemptCount }` | `{ prompts, attemptCount, guidanceHint? }` |

## UI Components

| Component | Props | Purpose |
|-----------|-------|---------|
| `StorySelection` | `stories[], questionId, jobId?` | Radio-button story picker with alignment verification |
| `StorySelectionList` | `stories[], onSelectionChange?` | Story list with per-item error boundaries |
| `StorySelectionConfirm` | `selectedStoryIds[], onConfirmed?` | Validates single selection, calls confirm API |
| `RecallScreen` | `progress?: RecallProgress` | Composes RecordButton + ProgressIndicator |
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

---

*Source: TDD plans 303–304, 306–309, 313–316 (session-1772314225364). All paths TLA+ verified.*
