# File Upload + Recall Questions Model TDD Implementation Plan

## Overview
Implement the orchestration defined in:
- `specs/orchestration/file-upload-recall-questions-model.md`
- `artifacts/tlaplus/file-upload-recall-questions-model/FileUploadRecallQuestions.tla`
- TLC config: `artifacts/tlaplus/file-upload-recall-questions-model/FileUploadRecallQuestions.cfg`

This adds three writer entry modes (`url`, `file_upload`, `default_questions`), default-question fallback, and per-question recall progression that advances to review.

TDD principle for each slice:
1. Write a failing test for one observable behavior.
2. Add minimal code to pass.
3. Refactor with tests green.

## Current State Analysis

### Key Discoveries
- Session start UI is URL-only today:
  - `frontend/src/modules/session/StartVoiceSessionModule.tsx:92` stores only `sourceUrl`
  - `frontend/src/modules/session/StartVoiceSessionModule.tsx:121` only calls `startSessionFromUrl(authToken, trimmedUrl)`
  - `frontend/src/modules/session/StartVoiceSessionModule.tsx:150` UX copy requires URL paste
- Session start contract is URL-only:
  - `frontend/src/api_contracts/startSessionFromUrl.ts:4` request schema has only `sourceUrl`
  - `frontend/src/api_contracts/startSessionFromUrl.ts:43` always posts to `/api/ingestion/url`
- URL backend route only validates URL ingestion path:
  - `frontend/src/app/api/ingestion/url/route.ts:29` validates `StartSessionFromUrlRequestSchema`
  - `frontend/src/app/api/ingestion/url/route.ts:41` always goes through `ChannelIngestionPipelineAdapter.initializeFromUrl`
- File upload API exists but is generic storage only:
  - `frontend/src/app/api/upload/route.ts:57` reads `formData.file`
  - `frontend/src/app/api/upload/route.ts:68` checks size, not MIME allowlist for this path
- Client file picker currently enforces only size/max count, not resume/screenshot type gates:
  - `frontend/src/components/chat/FileAttachment.tsx:63` size validation only
  - `frontend/src/components/chat/FileAttachment.tsx:14` audio MIME list is transcription-oriented, not writer input-mode policy
- Recall prompt is story-scoped, not question-scoped:
  - `frontend/src/components/RecallScreen.tsx:48` `buildRecallInstructions(selectedStory)`
  - `frontend/src/components/RecallScreen.tsx:65` `buildOpeningCoachPrompt(selectedStory)`
  - `frontend/src/components/RecallScreen.tsx:554` “Next question” only presents stop state; no question index progression
- Persisted recall state stores only working answer/turns, no per-question progress object:
  - `frontend/src/app/api/session/voice-turns/route.ts:20` response shape = `{ sessionId, workingAnswer, turns }`
  - `frontend/src/api_contracts/sessionVoiceTurns.ts:5` same shape on client contract
- Flow shell only reasons over broad stages; no explicit question queue state:
  - `frontend/src/modules/writingFlow.ts:19` only `RECALL | REVIEW`
  - `frontend/src/modules/WritingFlowModule.tsx:109` only valid steps are `RECALL`, `REVIEW`
- Existing test harness is strong and path-oriented:
  - `frontend/src/modules/session/__tests__/StartVoiceSessionModule.test.tsx:81`
  - `frontend/src/components/__tests__/RecallScreen.voice.test.tsx:145`
  - `frontend/__tests__/api/upload.test.ts:32`
  - `frontend/src/app/api/ingestion/url/__tests__/route.test.ts:40`

### TLA+/Spec Anchors
- Input modes and processing branches: spec Steps 1-2 (`specs/.../file-upload-recall-questions-model.md:42`)
- Resolve/default question behavior: Step 3 (`specs/...:68`)
- Question state and display: Steps 4-5 (`specs/...:84`, `specs/...:93`)
- Capture and advancement loops: Steps 6-7 (`specs/...:103`, `specs/...:114`)
- Terminal condition RECALL -> REVIEW: (`specs/...:124`)
- TLC constants and invariants to preserve: `FileUploadRecallQuestions.cfg:4-19`

## Desired End State

### Observable Behaviors
1. Given `/writer`, when user selects URL/file/default mode, then start session follows mode-specific branch and still enforces active-session conflict behavior.
2. Given file mode, when file set is invalid type/size, then client blocks submission and server rejects invalid payload with typed error.
3. Given default mode, when no external source is provided, then immutable default question bank is loaded.
4. Given session initialization success, when questions are resolved, then question progress is initialized and persisted with active question index.
5. Given recall screen for question `i`, when voice session starts, then coach instructions/opening prompt include only that active question.
6. Given transcript capture for active question, when user says next or required slots complete, then current question finalizes and index advances monotonically.
7. Given final question completion, when advancement runs, then flow transitions to `REVIEW` and no additional recall question is rendered.
8. Given errors (`SESSION_ALREADY_ACTIVE`, upload failure, extraction failure, voice retry exhaustion), when surfaced, then UI and API preserve existing typed error consistency.

## What We’re NOT Doing
- Replacing existing URL ingestion pipeline implementation details.
- Rewriting unrelated review/draft/finalize flows.
- Introducing client-side direct OpenAI calls.
- Shipping OCR/parser quality improvements beyond minimally testable extraction boundaries in this slice.

## Testing Strategy
- **Framework**: Vitest + Testing Library (`frontend/vitest.config.ts:8`, `frontend/package.json:11`).
- **Unit tests**:
  - Input mode mapping and validation helpers.
  - Question bank resolver and question-progress state transitions.
  - Recall prompt builders for question scoping.
- **Integration tests**:
  - `/writer` start flow with URL/file/default branches.
  - API route + handler + service interaction for file/default initialization.
  - Recall question advancement through persisted session state.
- **E2E tests**:
  - Happy path across all three input modes and final RECALL->REVIEW transition.
- **Verification commands**:
  - `npm --prefix frontend run test`
  - `npm --prefix frontend run type-check`
  - `npm --prefix frontend run lint`
  - `npm --prefix frontend run test:e2e`

## Behavior 1: Input Mode Selection Contract

### Test Specification
**Given** writer entry page
**When** user chooses URL, file upload, or default questions
**Then** UI state tracks `inputMode` as discriminated union and mode-specific controls render.

**Edge Cases**:
- Switching modes clears stale mode-specific errors.
- URL mode preserves existing required-url behavior.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/modules/session/__tests__/StartVoiceSessionModule.test.tsx`
- `frontend/src/app/writer/__tests__/page.start-session.test.tsx`

```ts
it('renders and switches input modes (url, file_upload, default_questions)', async () => {
  // assert mode controls and mode-specific UI sections
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/modules/session/StartVoiceSessionModule.tsx`
- Add `inputMode` state and segmented controls.
- Keep URL branch behavior untouched initially.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/modules/session/StartVoiceSessionModule.tsx`
- Extract mode-specific subcomponents (`UrlInputPanel`, `FileInputPanel`, `DefaultQuestionsPanel`) to reduce branching complexity.

### Success Criteria
**Automated:**
- [ ] New input-mode rendering tests fail first.
- [ ] Existing URL-only tests remain green (`StartVoiceSessionModule` reachability/error tests).

**Manual:**
- [ ] `/writer` visibly supports the three input modes.

---

## Behavior 2: File Upload Mode Validation + Init Branch

### Test Specification
**Given** file-upload mode
**When** user submits resume/screenshot files
**Then** accepted file types proceed, invalid types are rejected, upload endpoint + session initialization branch execute, and 409 conflicts are surfaced.

**Edge Cases**:
- Unsupported MIME type.
- File too large.
- Upload succeeds but extraction fails -> fallback/default path with explicit status.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/modules/session/__tests__/StartVoiceSessionModule.test.tsx`
- `frontend/__tests__/components/FileAttachment.test.tsx`
- `frontend/__tests__/api/upload.test.ts`

```ts
it('accepts only resume/screenshot types for writer file-upload mode', async () => {
  // assert reject/accept matrix from spec
});

it('starts session from uploaded file payload and navigates to /session/[id]', async () => {
  // mock upload + init contract
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/modules/session/StartVoiceSessionModule.tsx`
- `frontend/src/components/chat/FileAttachment.tsx` (or a writer-specific wrapper)
- `frontend/src/api_contracts/startSessionFromUpload.ts` (new)
- `frontend/src/app/api/session/start-from-upload/route.ts` (new)

Implementation target:
- Enforce extension/mime policy from spec (`resume: docx,doc,pdf,txt,md`; `screenshot: png,jpg,jpeg,webp`).
- Keep `SESSION_ALREADY_ACTIVE` mapping parity with URL branch.

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/modules/session/StartVoiceSessionModule.tsx`
- `frontend/src/api_contracts/startSessionFromUpload.ts`
- shared validation utility under `frontend/src/lib/`.

### Success Criteria
**Automated:**
- [ ] Upload mode tests cover success + unsupported type + oversize + 409.
- [ ] Existing upload route tests remain green (`frontend/__tests__/api/upload.test.ts`).

**Manual:**
- [ ] Resume-only, screenshot-only, and mixed upload flows create sessions.

---

## Behavior 3: Default Questions Initialization Branch

### Test Specification
**Given** default-questions mode
**When** user starts session with no external source
**Then** backend initializes session and resolves immutable default question bank (length > 0, ordered).

**Edge Cases**:
- Active session conflict returns same actionable message.
- Resolver failure falls back to default bank.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/modules/session/__tests__/StartVoiceSessionModule.test.tsx`
- `frontend/src/app/api/session/start-default/__tests__/route.test.ts` (new)

```ts
it('initializes session with default question bank when no input mode selected', async () => {
  // expect sessionId + initialized + question set metadata
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/api_contracts/startSessionDefaultQuestions.ts` (new)
- `frontend/src/app/api/session/start-default/route.ts` (new)
- `frontend/src/server/services/QuestionResolutionService.ts` (new)

Implementation target:
- Store default questions as exported server constant.
- Return initial question-progress payload.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/server/services/QuestionResolutionService.ts`
- Consolidate URL/file/default question resolution to one service with strategy branches.

### Success Criteria
**Automated:**
- [ ] Default mode tests fail then pass with fallback assertions.
- [ ] URL route tests remain green (`frontend/src/app/api/ingestion/url/__tests__/route.test.ts`).

**Manual:**
- [ ] Starting without URL/file produces first default question immediately.

---

## Behavior 4: Question State Persistence Contract

### Test Specification
**Given** resolved question list
**When** session enters recall-ready state
**Then** `questionProgress` (`currentIndex`, `total`, `completed`, `activeQuestionId`) is persisted and retrievable with working answer.

**Edge Cases**:
- Empty question set rejected.
- Persist failure returns typed error.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/app/api/session/voice-turns/__tests__/route.test.ts`
- `frontend/src/api_contracts/__tests__/sessionVoiceTurns.test.ts` (new)

```ts
it('returns questionProgress alongside workingAnswer and turns', async () => {
  // expect response includes currentIndex, total, activeQuestion
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/app/api/session/voice-turns/route.ts`
- `frontend/src/api_contracts/sessionVoiceTurns.ts`
- `frontend/src/server/data_access_objects/SessionDAO.ts`

Implementation target:
- Extend existing contract shape rather than create parallel endpoint.
- Persist question-progress JSON in durable storage.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/server/data_access_objects/SessionDAO.ts`
- Introduce typed mapper for question-progress payload to avoid untyped JSON field access.

### Success Criteria
**Automated:**
- [ ] Voice-turns route tests cover extended shape + backward compatibility.
- [ ] Existing working-answer reset/update tests still pass.

**Manual:**
- [ ] Reloading session keeps active question index/progress.

---

## Behavior 5: Recall Prompt Scoping to Active Question

### Test Specification
**Given** active question in progress
**When** RecallScreen builds realtime instructions/opening prompt
**Then** prompt includes only active question context (not full array or story-only prompt).

**Edge Cases**:
- Missing active question shows completion/review prompt.
- Move-on intent preserves incomplete-slot guidance for current question.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**File**: `frontend/src/components/__tests__/RecallScreen.voice.test.tsx`

```ts
it('passes active question text into realtime instructions and coach opening prompt', async () => {
  // assert connect called with instructions containing active question text
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/components/RecallScreen.tsx`
- Add `activeQuestion` prop/state.
- Update `buildRecallInstructions` and `buildOpeningCoachPrompt` signatures to include question text.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/components/RecallScreen.tsx`
- Extract pure prompt builders for direct unit test coverage.

### Success Criteria
**Automated:**
- [ ] RecallScreen voice tests include active-question assertions.
- [ ] Existing transcript submit/working-answer persistence tests remain green.

**Manual:**
- [ ] UI and spoken coach prompt reflect “Question X of Y” and active question text.

---

## Behavior 6: Question Advancement Loop

### Test Specification
**Given** active question response captured
**When** user explicitly selects next question or required slots complete
**Then** current question is marked completed, index increments monotonically, per-question slot state resets, and next question loads.

**Edge Cases**:
- Save failure blocks advancement.
- Last question transitions to review instead of incrementing past total.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/components/__tests__/RecallScreen.voice.test.tsx`
- `frontend/src/server/services/__tests__/RecallCompletionService.integration.test.ts`

```ts
it('advances to next question and resets per-question slot state', async () => {
  // assert currentIndex increments, completed contains prior question id
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/components/RecallScreen.tsx`
- `frontend/src/server/services/RecallCompletionService.ts`
- `frontend/src/server/services/VoiceRecallService.ts`

Implementation target:
- Add explicit `advanceQuestion` operation with persistence boundary.
- Preserve confirmed-slot non-overwrite rule per question instance.

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/server/services/RecallCompletionService.ts`
- `frontend/src/server/services/VoiceRecallService.ts`
- Create `QuestionProgressService.ts` (new) if orchestration logic grows.

### Success Criteria
**Automated:**
- [ ] Progress monotonicity tested across multiple advances.
- [ ] Retry/error semantics for voice capture remain intact.

**Manual:**
- [ ] “Next question” actually advances question text and progress indicator.

---

## Behavior 7: Terminal Transition to REVIEW

### Test Specification
**Given** final question is completed (or remaining skipped)
**When** advancement is evaluated
**Then** session transitions from recall to review stage and Recall screen no longer displays question capture controls.

**Edge Cases**:
- Review transition persistence failure returns recoverable error.
- Refresh after terminal transition lands in review.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/modules/__tests__/WritingFlowModule.rendering.test.tsx`
- `frontend/src/modules/__tests__/RecallModule.integration.test.tsx`
- `frontend/src/app/session/[sessionId]/__tests__/page.flow.integration.test.tsx`

```ts
it('transitions RECALL -> REVIEW when questionProgress.currentIndex reaches total', async () => {
  // assert ReviewScreen render and recall controls hidden
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/modules/writingFlow.ts`
- `frontend/src/modules/WritingFlowModule.tsx`
- `frontend/src/modules/session/SessionWorkflowShell.tsx`

Implementation target:
- Wire question-progress terminal state to `NavigationIntent { targetStep: 'REVIEW' }`.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/modules/WritingFlowModule.tsx`
- Move terminal-condition check into dedicated hook (`useRecallCompletionTransition`) for clearer tests.

### Success Criteria
**Automated:**
- [ ] Rendering and route-level integration tests verify terminal transition.
- [ ] Existing return-to-recall tests remain green.

**Manual:**
- [ ] Completing final question lands user on review without manual refresh.

---

## Behavior 8: Error Consistency and Regression Guardrails

### Test Specification
**Given** known failures across URL/file/default + voice capture
**When** errors occur
**Then** code/message/status contracts remain consistent with modeled invariants and existing UI handling.

**Edge Cases**:
- `SESSION_ALREADY_ACTIVE` on all three start paths.
- Empty transcript retry and escalation path preserved.
- Upload/extraction errors produce typed codes and actionable UI messages.

### TDD Cycle
#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/modules/session/__tests__/StartVoiceSessionModule.test.tsx`
- `frontend/src/app/api/ingestion/url/__tests__/route.test.ts`
- `frontend/__tests__/api/upload.test.ts`
- `frontend/src/server/services/__tests__/captureSpokenInput.test.ts`

```ts
it('maps SESSION_ALREADY_ACTIVE consistently across url/file/default start contracts', async () => {
  // assert shared actionable UI copy and 409 semantics
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- Start-session contract modules/routes (URL/file/default)
- Error mapping helper in session-start module.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/modules/session/StartVoiceSessionModule.tsx`
- Consolidate branch-specific error mapping in one `mapStartSessionErrorToUiMessage` extension.

### Success Criteria
**Automated:**
- [ ] Regression suite validates invariant parity with current URL flow and voice retries.

**Manual:**
- [ ] User sees consistent, actionable failures regardless of input mode.

---

## TLC/TLA+ Verification Track

### Model + Config Alignment
- Primary model: `artifacts/tlaplus/file-upload-recall-questions-model/FileUploadRecallQuestions.tla`
- Primary TLC config: `artifacts/tlaplus/file-upload-recall-questions-model/FileUploadRecallQuestions.cfg`
- Secondary config found in tree: `FileUploadRecallQuestionsModel.cfg` (retain for compatibility; use primary config above for this path unless project tooling explicitly points elsewhere).

### Checklist
- [ ] TLC run validates `TypeInvariant`, `QuestionsNonEmpty`, `SingleActiveQuestion`, `ErrorPropagation`, `ResumeStoredBeforeQuestions`.
- [ ] Liveness property reaches `review` or `error` terminal states.
- [ ] Each implemented behavior maps to at least one invariant/test oracle from spec table (`INV-1` ... `INV-12`).

## Integrated Verification Commands
```bash
npm --prefix frontend run test -- src/modules/session/__tests__/StartVoiceSessionModule.test.tsx
npm --prefix frontend run test -- src/components/__tests__/RecallScreen.voice.test.tsx
npm --prefix frontend run test -- src/app/api/session/voice-turns/__tests__/route.test.ts
npm --prefix frontend run test -- src/app/api/ingestion/url/__tests__/route.test.ts
npm --prefix frontend run test -- __tests__/api/upload.test.ts
npm --prefix frontend run test -- src/server/services/__tests__/captureSpokenInput.test.ts
npm --prefix frontend run test
npm --prefix frontend run type-check
npm --prefix frontend run lint
npm --prefix frontend run test:e2e
```

## References
- Spec: `specs/orchestration/file-upload-recall-questions-model.md`
- TLA+: `artifacts/tlaplus/file-upload-recall-questions-model/FileUploadRecallQuestions.tla`
- TLC: `artifacts/tlaplus/file-upload-recall-questions-model/FileUploadRecallQuestions.cfg`
- Core implementation anchors:
  - `frontend/src/modules/session/StartVoiceSessionModule.tsx:92`
  - `frontend/src/components/RecallScreen.tsx:48`
  - `frontend/src/server/services/VoiceRecallService.ts:193`
  - `frontend/src/api_contracts/startSessionFromUrl.ts:4`
  - `frontend/src/app/api/ingestion/url/route.ts:29`
  - `frontend/src/app/api/upload/route.ts:57`
  - `frontend/src/app/api/session/voice-turns/route.ts:20`
  - `frontend/src/modules/writingFlow.ts:19`
- Core test anchors:
  - `frontend/src/modules/session/__tests__/StartVoiceSessionModule.test.tsx:81`
  - `frontend/src/components/__tests__/RecallScreen.voice.test.tsx:145`
  - `frontend/src/server/services/__tests__/captureSpokenInput.test.ts:82`
  - `frontend/src/app/api/ingestion/url/__tests__/route.test.ts:40`
  - `frontend/__tests__/api/upload.test.ts:32`
