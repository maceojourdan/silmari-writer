# Session Initialization & Setup

**Domain:** Session creation, resume/job/question ingestion, consent, voice session start
**Paths:** 293–295, 302, 310–312
**Priority:** P0

---

## Overview

Handles the first phase of the voice loop: user uploads a resume, pastes a job posting and question, and the system initializes a session with structured objects. Includes consent-gated voice session start and session creation with state tracking.

## State Machine

```
[No Session] → INIT → ORIENT
```

- **INIT**: Session created with resume, job, and question objects parsed and validated
- **ORIENT**: Automatic transition after successful initialization

## API Endpoints

| Method | Path | Request | Response | Auth |
|--------|------|---------|----------|------|
| `POST` | `/api/sessions` | — (userId from auth) | `{ sessionId, state }` | Bearer token via `AuthAndValidationFilter` |
| `POST` | `/api/sessions/initialize` | `{ resume: ResumeObject, job: JobObject, question: QuestionObject }` | `{ id, resume, job, question, state }` | None |
| `POST` | `/api/session/init` | `SessionInitInputSchema` | Session init result | None |
| `POST` | `/api/voice-session/start` | `{ consent: boolean }` | `{ sessionStatus }` | None |

## Data Structures

### ResumeObject
```ts
{
  roles: Array<{ company, title, dates, bullets[], tools[], outcomes[] }>;
  skills: string[];
  projects?: Array<{ name, description }>;
  education: Array<{ institution, degree, year }>;
}
```

### JobObject
```ts
{
  title: string;
  company: string;
  requirements_required: string[];
  requirements_preferred: string[];
  responsibilities: string[];
  keywords: string[];
  level: 'junior' | 'mid' | 'senior';
}
```

### QuestionObject
```ts
{
  question_text: string;
  question_type: 'behavioral_STAR' | 'technical' | 'leadership' | 'conflict' | 'motivation' | 'culture' | 'open_ended';
  evaluation_targets: string[];
}
```

## UI Components

| Component | File | Purpose |
|-----------|------|---------|
| `VoiceSessionStart` | `components/VoiceSessionStart.tsx` | Consent toggle + start button |
| `SessionInitForm` | `components/SessionInitForm.tsx` | Resume/job/question upload |

## Database Entities

| Table | Key Fields |
|-------|------------|
| `sessions` | `id`, `user_id`, `status`, `resume_object`, `job_object`, `question_object`, `created_at` |
| `resumes` | `id`, structured resume data |
| `jobs` | `id`, structured job data |
| `questions` | `id`, question text, type, evaluation targets |

## Error Catalog

| Code | HTTP | Condition |
|------|------|-----------|
| `INVALID_REQUEST_FORMAT` | 400 | Malformed JSON body |
| `SESSION_ERROR` | 500 | Session creation failure |
| `CONSENT_ERROR` | 422 | Consent not provided or invalid |
| `UNAUTHORIZED` | 401 | Missing/invalid auth header |

## Resource UUIDs

| UUID | Name | Implementation |
|------|------|----------------|
| `ui-w8p2` | component | `VoiceSessionStart.tsx` |
| `ui-a4y1` | frontend_verifier | `SessionInitVerifier.ts` |
| `api-q7v1` | frontend_api_contract | `initSession.ts` |
| `api-m5g7` | endpoint | `session/init/route.ts` |
| `api-n8k2` | request_handler | `InitSessionRequestHandler.ts` |
| `api-p3e6` | filter | `AuthAndValidationFilter.ts` |

---

*Source: TDD plans 293–295, 302, 310–312 (session-1772314225364). All paths TLA+ verified.*
