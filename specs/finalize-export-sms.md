# Finalization, Export & SMS Follow-up

**Domain:** Answer finalization, locking, export/copy, SMS follow-up, voice editing, navigation
**Paths:** 305, 330–337
**Priority:** P0

---

## Overview

After review approval, the system finalizes the answer (locking it from further edits), enables export/copy, and optionally sends SMS follow-up messages for uncertain claims. Voice editing and return-to-recall navigation are available during the review phase before finalization.

## State Machine

```
REVIEW ──(approve)──→ FINALIZE ──(smsOptIn?)──→ FOLLOWUP_SMS
                                                 └─(no SMS)──→ done

REVIEW ──(return to recall)──→ RECALL
REVIEW ──(edit by voice)──→ [voice edit] ──→ REVIEW
```

### Answer Locking
```
status: COMPLETED → FINALIZED
finalized: false → true
editable: true → false
locked: false → true
```

All four fields written atomically in a single DAO call.

## API Endpoints

| Method | Path | Request | Response | Error Codes |
|--------|------|---------|----------|-------------|
| `POST` | `/api/answers/[id]/finalize` | Path param `id` | `{ id, finalized: true, editable: false }` | 401, 404, 409, 422, 500 |
| `GET` | `/api/answers/[id]/export` | `?format=markdown\|plain_text` | `{ content, format, answerId }` | 400, 404, 422, 500 |
| `PUT` | `/api/answers/[id]` | `{ content }` | `{ id, content }` | 401, 403, 404, 500 |
| `POST` | `/api/edit-by-voice` | `{ contentId, instructionText }` | `{ updatedContent }` | 422, 500 |
| `POST` | `/api/sms/webhook` | Twilio payload | `{ status, claimId, newStatus }` | 400 |

## Export Formats

| Format | Extension | MIME Type |
|--------|-----------|-----------|
| Plain text | `.txt` | `text/plain` |
| Markdown | `.md` | `text/markdown` |

Export creates a Blob download; Copy uses `navigator.clipboard.writeText()`.

## SMS Follow-up Flow

### Trigger Conditions (all must hold)
1. `user.smsOptIn === true`
2. `user.phoneNumber` matches E.164 format
3. One or more: session ended before VERIFY, draft has uncertain claims, confidence < 0.7, missing metric/artifact

### Message Types (max 3 per session)
| Type | Template |
|------|----------|
| Y/N Approval | "Quick check: does this line sound accurate? '…' Reply Y/N" |
| Two-choice | "Which is closer: saved hours/week (A) or days/month (B)?" |
| Fill numeric | "About how many people were on the project team?" |
| Artifact prompt | "Was there a PR/ticket/doc? Reply PR / Ticket / Doc / None" |

### Send Pipeline
```
detectFinalizeCompletion → loadAnswerAndContact → composeSmsMessage (≤160 chars)
  → sendSms (Twilio, retry max 3, exponential backoff) → SmsFollowUpDAO.insert
```

### Reply Handling
```
POST /api/sms/webhook → SmsReplyTransformer.parse → TruthCheckReplyProcessor
  → ClaimDAO.updateTruthCheck → claim status updated
```

## UI Components

| Component | Props | Purpose |
|-----------|-------|---------|
| `FinalizeAnswerButton` | `answerId, editable` | Finalize with editable guard |
| `ExportCopyControls` | `answerId, finalized, locked` | Export/copy with finalized gate |
| `AnswerEditor` | `answerId, initialContent` | Edit with lock detection |
| `EditByVoiceComponent` | `contentId` | Voice capture with 3-retry limit |
| `ReviewScreen` | `selectedContentId?` | Review with voice edit + return-to-recall |
| `WritingFlowModule` | — | RECALL/REVIEW step navigation |

## Database Entities

| Table | Key Fields |
|-------|------------|
| `answers` | `id`, `content`, `status`, `finalized`, `editable`, `locked`, `userId` |
| `sms_follow_ups` | `id`, `answerId`, `userId`, `status`, `phoneNumber`, `message` |
| `users` | `id`, `smsOptIn`, `phoneNumber` |
| `content` | `id`, `body` (voice edit target) |

## Locking Rules

| Precondition | Error if violated |
|---|---|
| Answer exists | `ANSWER_NOT_FOUND` (404) |
| `status === 'COMPLETED'` | `ANSWER_NOT_COMPLETED` (422) |
| `finalized === false` | `ANSWER_ALREADY_FINALIZED` (409) |

**Edit prevention:** Backend checks `answer.locked === true` before any update → `LOCKED_ANSWER_MODIFICATION_FORBIDDEN` (403).

**Known issue:** TOCTOU race between read and update. Production fix: atomic `UPDATE ... WHERE locked = false`.

## Error Catalog

| Code | HTTP | Condition |
|------|------|-----------|
| `ANSWER_NOT_FOUND` | 404 | DAO returns null |
| `ANSWER_NOT_COMPLETED` | 422 | Status not COMPLETED |
| `ANSWER_ALREADY_FINALIZED` | 409 | Already finalized |
| `LOCKED_ANSWER_MODIFICATION_FORBIDDEN` | 403 | Answer locked |
| `UNSUPPORTED_EXPORT_FORMAT` | 400/422 | Invalid format |
| `PROVIDER_FAILURE` | 502 | Twilio retries exhausted |
| `VOICE_CAPTURE_FAILED` | 422 | Voice capture failure (retryable) |
| `INVALID_INSTRUCTION` | 422 | Voice instruction unparseable |
| `CLAIM_NOT_FOUND` | 400 | SMS reply correlation failure |

---

*Source: TDD plans 305, 330–337 (session-1772314225364). All paths TLA+ verified.*
