# PATH: file-upload-recall-questions-model

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from existing code — `StartVoiceSessionModule.tsx`, `RecallScreen.tsx`, `VoiceRecallService.ts`, `startSessionFromUrl.ts`, `writingFlow.ts`

## Purpose

Behavioral model for adding file uploads (resume/screenshot) to the writer component
and introducing default recall questions when no URL is provided. Currently, the writer
workflow requires a job URL to initialize a session. This change adds two alternative
input modes: (1) file upload (resume or job screenshot), and (2) no external input
(uses default questions). The Recall page must display questions one at a time, and the
voice AI must receive questions individually with tracked question state and progress.

Current behavior captured as a verifiable baseline. Proposed changes extend the
session initialization path and recall question delivery loop.

## Trigger

User navigates to `/writer` and interacts with `StartVoiceSessionModule` to begin a
voice-assisted answer session via one of three input modes: URL, file upload, or
no-input (default questions).

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-v3n6` | StartVoiceSessionModule | Entry point: input mode selection (URL / file / default) |
| `ui-w8p2` | RecallScreen | Recall step UI: question display + voice capture |
| `db-h2s4` | VoiceRecallService | Voice capture loop (5 steps) |
| `cfg-k3x7` | VoicePromptTemplates | Prompt templates for follow-up questions |
| `api-u1r9` | startSessionFromUrl | URL-based session init contract |
| `api-f2k8` | upload API | File upload to Vercel Blob storage |
| `db-r5m3` | resumes table | Resume content storage (id, content, name, word_count) |
| `fn-q4w2` | buildRecallInstructions | Constructs coach instructions for voice AI |
| `fn-d7j1` | buildOpeningCoachPrompt | Constructs initial greeting/question |

## Steps

1. **SelectInputMode**
   - Input: User on `/writer` page, authenticated via `RequireAuth`
   - Process: User chooses one of three input modes:
     - **URL mode**: Paste a job posting URL (existing behavior)
     - **File upload mode**: Upload resume (docx, doc, pdf, txt, md) or job screenshot (png, jpg, webp)
     - **No-input mode**: Skip to default questions
   - Output: `InputMode = 'url' | 'file_upload' | 'default_questions'`
   - Error: Unauthenticated -> redirect to `/login`

2. **ProcessInput**
   - Input: `InputMode` + associated data (URL string | File[] | nothing)
   - Process:
     - **URL mode**: Call `startSessionFromUrl(authToken, sourceUrl)` -> session with job context
     - **File upload mode**:
       - Validate file types (resume: `.docx,.doc,.pdf,.txt,.md`; screenshot: `.png,.jpg,.jpeg,.webp`)
       - Upload via `POST /api/upload` -> blob URL
       - If resume: extract text content, store in `resumes` table
       - If screenshot: store blob reference on session
       - Initialize session with extracted/partial context
     - **No-input mode**: Initialize session with `source_type = 'default'`, no job context
   - Output: `{ sessionId: uuid, state: 'initialized', inputMode: InputMode, resumeId?: uuid }`
   - Error:
     - URL mode: `SESSION_ALREADY_ACTIVE` (409) | network failure | invalid URL
     - File mode: file too large (>10MB) | unsupported type | upload failure | extraction failure
     - No-input mode: `SESSION_ALREADY_ACTIVE` (409)

3. **ResolveQuestions**
   - Input: `{ sessionId, inputMode, jobContext?: string, resumeContent?: string }`
   - Process:
     - **URL mode** (existing): Questions derived from job posting context by LLM pipeline
     - **File upload mode**:
       - If resume + job screenshot: derive questions from both
       - If resume only: use default questions with resume context overlay
       - If screenshot only: extract job context from image, derive questions
     - **No-input mode**: Load default question bank:
       1. "Tell us about your favourite project you worked on in recent memory and why you loved working on it so much."
       2. "What's the biggest change you've seen in your industry in the last year, and how have you changed your approach in response?"
       3. "What about this role are you most interested in or excited about?"
       4. "What recent update, industry change, or new industry opportunity are you most excited about right now?"
   - Output: `Question[] = Array<{ id: string, text: string, category: string, position: number }>`
   - Error: LLM derivation failure -> fallback to default questions (graceful degradation)

4. **InitializeQuestionState**
   - Input: `{ sessionId, questions: Question[] }`
   - Process:
     - Create `QuestionProgress` tracker: `{ currentIndex: 0, total: questions.length, completed: [], active: questions[0] }`
     - Persist question set to session (session.question JSONB field)
     - Set session into RECALL-ready state
   - Output: `QuestionProgress = { currentIndex: number, total: number, completed: string[], active: Question }`
   - Error: Session not found | invalid question set (empty array)

5. **DisplayRecallQuestion**
   - Input: `QuestionProgress` with `active: Question`
   - Process:
     - RecallScreen renders current question text prominently
     - `buildRecallInstructions(selectedStory, activeQuestion)` includes question text in coach instructions
     - `buildOpeningCoachPrompt(selectedStory, activeQuestion)` presents the question as the opening prompt
     - Voice AI receives question-scoped context (one question at a time)
   - Output: UI shows question text + coach prompt + record button + progress indicator (e.g., "Question 1 of 4")
   - Error: No active question -> display completion state

6. **CaptureQuestionResponse**
   - Input: Voice audio or text input for the active question
   - Process:
     - Voice: `VoiceRecallService.captureSpokenInput()` -> transcript -> slot extraction
     - Text: Direct working answer editing
     - Merge into working answer for this specific question
     - Persist via `updateSessionWorkingAnswer()`
     - Track progress: anchors/actions/outcomes per-question
   - Output: `{ transcript: string, workingAnswer: string, questionProgress: RecallProgress }`
   - Error: Voice recognition failed | empty transcript | save failure -> retry with status messaging

7. **AdvanceToNextQuestion**
   - Input: User signals completion (explicit "Next question" or all slots filled)
   - Process:
     - Save current question's working answer as completed
     - Increment `currentIndex` in `QuestionProgress`
     - If `currentIndex < total`: load next question, reset per-question progress, return to Step 5
     - If `currentIndex >= total`: all questions answered, transition to REVIEW step
   - Output: Updated `QuestionProgress` | transition to REVIEW
   - Error: Save failure on current answer -> block advancement, show error

## Terminal Condition

All questions have been answered (or user explicitly skips remaining). Session transitions
from RECALL to REVIEW step via `WritingFlowModule` navigation. Caller (`WritingFlowModule`)
observes `activeStep === 'REVIEW'` with all question responses persisted.

## Feedback Loops

Per-question voice recall loop repeats Steps 5-6 within a single question with a maximum of 3 slot captures (anchors, actions, outcomes) before auto-advancing; user may also explicitly advance at any time via "Next question".

Question advancement loop repeats Steps 5-6-7 for each question with a maximum of `questions.length` iterations (max 4 for default questions) before transitioning to REVIEW.

Voice retry loop within Step 6 retries failed transcription with a maximum of 3 attempts (maxRetries) before escalating to VOICE_RECOGNITION_FAILED error.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | Every input mode produces a valid sessionId | `StartVoiceSessionModule.tsx:121-130` | Reachability | All three paths (URL/file/default) return `{ sessionId: uuid, state: 'initialized' }` |
| INV-2 | File uploads validate type before upload | `FileAttachment.tsx:48-79` | TypeInvariant | Only accepted MIME types proceed past validation |
| INV-3 | No-URL sessions always have >= 1 question | Step 3 design | TypeInvariant | `questions.length > 0` after ResolveQuestions for all input modes |
| INV-4 | Voice AI receives exactly one question at a time | Step 5 design | TypeInvariant | `buildRecallInstructions` receives single `activeQuestion`, not array |
| INV-5 | Question index monotonically increases | Step 7 design | Reachability | `currentIndex` only increments, never decrements or resets mid-session |
| INV-6 | All questions reachable from trigger | Steps 5-7 loop | Reachability | For `questions.length = N`, steps 5-7 execute exactly N times before terminal |
| INV-7 | Resume content stored before session proceeds | Step 2 (file mode) | Reachability | `resumes` table row exists with `content.length > 0` before Step 3 |
| INV-8 | Confirmed slots not overwritten | `VoiceRecallService.ts:306-312` | TypeInvariant | `updateSlotState` skips slots where `confirmed === true` |
| INV-9 | Empty transcript triggers retry, not silent failure | `VoiceRecallService.ts:222-241` | ErrorConsistency | Empty transcript throws `VOICE_RECOGNITION_FAILED` (retryable) |
| INV-10 | Question progress visible to user at all times | Step 5 design | Reachability | Progress indicator shows `currentIndex + 1` of `total` whenever RecallScreen is mounted |
| INV-11 | Default questions are immutable constants | Step 3 design | TypeInvariant | Default question bank is a `const` array, not mutable state |
| INV-12 | Session error (409) propagates on all input modes | `startSessionFromUrl.ts:56-61`, Step 2 | ErrorConsistency | `SESSION_ALREADY_ACTIVE` is surfaced to UI for URL, file, and default modes |

## Change Impact Analysis

**Proposed change:** Add file upload (resume/screenshot) and default-question fallback to writer workflow. Extend Recall to display questions one at a time with voice AI tracking.

**Affected steps:**
- Step 1 (SelectInputMode): NEW — currently only URL mode exists
- Step 2 (ProcessInput): EXTENDED — add file upload and no-input branches
- Step 3 (ResolveQuestions): NEW — currently questions come from URL-derived job context only
- Step 4 (InitializeQuestionState): NEW — no per-question tracking exists today
- Step 5 (DisplayRecallQuestion): MODIFIED — RecallScreen currently shows story, not question text
- Step 6 (CaptureQuestionResponse): MODIFIED — add per-question scoping to existing voice loop
- Step 7 (AdvanceToNextQuestion): NEW — no multi-question navigation exists today

**Affected invariants:**
- INV-1 (session from all modes): New paths must satisfy existing session contract
- INV-4 (one question at a time): New constraint — voice AI currently gets story context, not question
- INV-8 (confirmed slots): Existing invariant preserved — slot state resets between questions

**Risk:**
- Breaking the URL-only path while adding alternatives (regression)
- Question state leaking between questions (stale slots from Q1 appearing in Q2)
- File parsing failures (docx/pdf) not gracefully degrading to default questions
- Resume storage without proper user scoping (multi-tenant safety)

**Recommendation:**
- Extract `InputMode` as a discriminated union early in the pipeline
- Question state machine should be a separate module (`QuestionProgressModule`) with explicit reset between questions
- Default questions should be a server-side constant, not client-derived
- File parsing should be async with a loading state + fallback to default questions on failure
- Test each input mode independently, then test transitions between questions
