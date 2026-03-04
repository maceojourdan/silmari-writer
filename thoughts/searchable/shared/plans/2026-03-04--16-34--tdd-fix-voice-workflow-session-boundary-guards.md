# Voice Workflow Session Boundary Guards TDD Implementation Plan

## Overview
Fix `INVALID_STATE: Session <id> not found` during Recall transcript save by enforcing the boundary between two intentional workflows:
- `sessions` (`state: initialized`) for prep/session flow
- `answer_sessions` (`state: INIT|IN_PROGRESS|RECALL|...`) for voice-response flow

This plan does **not** merge the models. It makes routing and error semantics explicit so IDs cannot be mixed silently.

## Review-Driven Amendments (2026-03-04)
This revision incorporates debug review findings that must be addressed for a correct fix:
1. **Durability gap**: current legacy persistence path can return success without writing anything.
2. **Security gap**: explicit source-mismatch messaging on an unauthenticated endpoint can leak record existence/type.
3. **Fail-open client gap**: missing `sessionSource` currently defaults to voice-response behavior.
4. **Testing gap**: current scenarios assert immediate UI success but not durable read-back.

## Current State Analysis

### Key Discoveries
- Start routes still allocate prep `sessions` IDs via `InitializeSessionService.createSession`:
  - `frontend/src/app/api/session/start-default/route.ts:31`
  - `frontend/src/app/api/session/start-from-upload/route.ts:287`
  - `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts:37`
- Session load is mixed-source by design (`answer_sessions` first, then `sessions`):
  - `frontend/src/server/request_handlers/GetSessionHandler.ts:9`
  - `frontend/src/server/request_handlers/GetSessionHandler.ts:24`
- Stage mapping routes legacy `initialized` into Recall/Review:
  - `frontend/src/modules/session/stageMapper.ts:16`
- Recall currently always posts final transcript to `/api/session/voice-response` when connected:
  - `frontend/src/components/RecallScreen.tsx:469`
- Voice-response handler validates only `answer_sessions` and throws `INVALID_STATE` on miss:
  - `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts:60`
  - `frontend/src/server/data_access_objects/SessionDAO.ts:368`
- Voice-turns route currently allows silent no-op behavior for legacy IDs with no backing story row:
  - `frontend/src/server/data_access_objects/SessionDAO.ts:540`
  - `frontend/src/app/api/session/voice-turns/route.ts:111`
- Existing tests cover seams but not all required guarantees:
  - `frontend/src/components/__tests__/RecallScreen.voice.test.tsx`
  - `frontend/src/server/request_handlers/__tests__/ProcessVoiceResponseHandler.test.ts`
  - `frontend/src/app/api/session/voice-response/__tests__/route.test.ts`
  - `frontend/src/modules/session/__tests__/SessionWorkflowShell.test.tsx`
  - `frontend/src/modules/session/__tests__/stageMapper.test.ts`

## Desired End State
- Recall only calls `/api/session/voice-response` when loaded `session.source === 'answer_session'`.
- Legacy `source='session'` Recall transcripts persist through an explicitly defined, durable path.
- Legacy durability is **provable by read-back** after write (no false “saved” status).
- `sessionSource` is required through client wiring (fail-closed; no implicit fallback to answer-session flow).
- `/api/session/voice-response` returns mismatch guidance only under authenticated/authorized context.
- Existing start-route contracts (`state='initialized'`) and finalize lifecycle remain unchanged.

### Observable Behaviors
- Given `source='session'` and no existing legacy story record, when final transcript event arrives, then the backend creates or updates a prep-linked persisted record and read-back returns the same content.
- Given `source='answer_session'`, when final transcript event arrives, then current `submitVoiceResponse` progression remains unchanged.
- Given a legacy `sessions.id` posted to `/api/session/voice-response` by an authenticated owner, then it returns `INVALID_STATE` with explicit source-mismatch guidance.
- Given unauthenticated or unauthorized caller, voice-response does not disclose cross-workflow existence/type details.
- Given current start/finalize paths, when regression suites run, then no contract or lifecycle behavior changes.

## What We're NOT Doing
- Migrating start routes to `answer_sessions` in this fix.
- Renaming all models/routes to PrepSession/VoiceSession in this fix.
- Changing finalize ownership from `sessions` to `answer_sessions`.
- Backfilling historical records.

## Testing Strategy
- **Framework**: Vitest + React Testing Library
- **Test types**:
  - DAO + route durability tests for legacy persistence semantics
  - Component wiring tests for source propagation and fail-closed behavior
  - Component behavior tests for source-aware transcript submission
  - Route/handler tests for auth + mismatch error contracts
  - Regression tests for stage mapping, start contracts, finalize invariants
- **Order**:
  1. Durable legacy persistence contract
  2. Source wiring + fail-closed client behavior
  3. Source-aware Recall submit behavior
  4. Auth/ownership + mismatch error semantics
  5. Regression sweeps

## Behavior 0: Define Durable Legacy Persistence Contract

### Test Specification
**Given** `sessionSource='session'` and no `story_records` row for that prep session  
**When** working answer is persisted through voice-turns  
**Then** backend creates a prep-linked record (via `story_records.session_id`) and returns persisted content.

**Given** an existing prep-linked record  
**When** working answer updates  
**Then** it updates in place (no duplicate row).

**Edge Cases**
- If prep session exists but `user_id` is missing, fail explicitly (do not return a false saved result).
- Legacy writes must never target `voice_session_id` path.
- Read path and write path must use the same source-specific lookup strategy.

### TDD Cycle

#### Red: Write Failing Tests
**Files**:
- `frontend/src/server/data_access_objects/__tests__/SessionDAO.wiring.test.ts`
- `frontend/src/app/api/session/voice-turns/__tests__/route.test.ts`
- `frontend/src/api_contracts/__tests__/sessionVoiceTurns.test.ts`

```ts
it('creates legacy story record on first write for source=session and returns durable value', async () => {
  // POST update_working_answer with sessionSource=session
  // then GET voice-turns with same source returns persisted content
});

it('does not report success when no durable write occurred', async () => {
  // ensure route returns explicit error instead of optimistic response
});
```

#### Green: Minimal Implementation
**Files**:
- `frontend/src/api_contracts/sessionVoiceTurns.ts`
- `frontend/src/app/api/session/voice-turns/route.ts`
- `frontend/src/server/data_access_objects/SessionDAO.ts`

```ts
// Add explicit source field to voice-turns contracts:
// sessionSource: 'answer_session' | 'session'

// Add source-aware DAO methods:
// findStoryRecordByVoiceSessionId(id)
// findStoryRecordByPrepSessionId(id)
// upsertPrepStoryRecordWorkingAnswer(prepSessionId, content)

// Remove silent success path when write did not persist.
```

#### Refactor: Improve Code
**Files**:
- `frontend/src/server/data_access_objects/SessionDAO.ts`
- `frontend/src/app/api/session/voice-turns/route.ts`

```ts
// Extract resolveStoryRecordBySource() and persistWorkingAnswerBySource() helpers.
```

### Success Criteria
**Automated:**
- [x] New DAO + route durability tests fail first, then pass.
- [x] `sessionVoiceTurns` contract tests include source field validation.
- [x] `npm --prefix frontend run test -- src/server/data_access_objects/__tests__/SessionDAO.wiring.test.ts src/app/api/session/voice-turns/__tests__/route.test.ts src/api_contracts/__tests__/sessionVoiceTurns.test.ts`

**Manual:**
- [ ] For legacy session, write answer, refresh, and verify read-back contains same value.

---

## Behavior 1: Thread Session Source to Recall (Fail-Closed)

### Test Specification
**Given** `SessionWorkflowShell` receives mixed-source `SessionView`  
**When** it renders Recall path  
**Then** it forwards `session.source` down to `RecallScreen` as required prop.

**Given** source is missing in wiring  
**When** Recall submit path is evaluated  
**Then** it fails closed (no voice-response fallback).

**Edge Cases**
- Existing `INIT + answer_session + no questionId` primary-entry behavior remains unchanged.
- Existing ORIENT behavior for `INIT + answer_session + questionId` remains unchanged.

### TDD Cycle

#### Red: Write Failing Test
**Files**:
- `frontend/src/modules/session/__tests__/SessionWorkflowShell.test.tsx`
- `frontend/src/modules/session/__tests__/stageMapper.test.ts`
- `frontend/src/components/__tests__/RecallScreen.voice.test.tsx`

```tsx
it('forwards session.source into WritingFlowModule and RecallScreen', () => {
  // expect sessionSource to be present and correct
});

it('does not submit transcript when sessionSource is undefined', async () => {
  // fail-closed assertion
});
```

#### Green: Minimal Implementation
**Files**:
- `frontend/src/modules/session/SessionWorkflowShell.tsx`
- `frontend/src/modules/WritingFlowModule.tsx`
- `frontend/src/components/RecallScreen.tsx`

```tsx
type SessionSource = 'answer_session' | 'session';
// Make sessionSource required in RecallScreen on live path.
```

#### Refactor: Improve Code
**File**:
- `frontend/src/modules/WritingFlowModule.tsx`

```tsx
// Keep prop names explicit and narrow to avoid generic sessionId-only ambiguity.
```

### Success Criteria
**Automated:**
- [x] New source-forwarding + fail-closed assertions fail first, then pass.
- [x] Stage and primary-entry tests remain green.
- [x] `npm --prefix frontend run test -- src/modules/session/__tests__/SessionWorkflowShell.test.tsx src/modules/session/__tests__/stageMapper.test.ts src/components/__tests__/RecallScreen.voice.test.tsx`

**Manual:**
- [ ] `/session/:id` renders same stage as before for both source types.

---

## Behavior 2: Make Recall Transcript Persistence Source-Aware

### Test Specification
**Given** Recall is connected and receives final transcript events  
**When** `sessionSource` is `session`  
**Then** it skips `submitVoiceResponse`, persists through source-aware voice-turns write, and reports saved status only on durable success.

**Given** `sessionSource` is `answer_session`  
**When** final transcript arrives  
**Then** it keeps current `submitVoiceResponse` behavior.

**Edge Cases**
- Move-on intent transcripts still avoid persistence submit.
- Dedupe key behavior remains unchanged.

### TDD Cycle

#### Red: Write Failing Tests
**File**:
- `frontend/src/components/__tests__/RecallScreen.voice.test.tsx`

```tsx
it('does not call submitVoiceResponse when sessionSource is session', async () => {
  render(<RecallScreen sessionId={SESSION_ID} sessionSource="session" />);
  emitVoiceEvent(finalTranscriptEvent);
  await waitFor(() => {
    expect(mockSubmitVoiceResponse).not.toHaveBeenCalled();
    expect(mockUpdateSessionWorkingAnswer).toHaveBeenCalledWith(
      SESSION_ID,
      expect.any(String),
      'session',
    );
  });
});

it('still calls submitVoiceResponse when sessionSource is answer_session', async () => {
  render(<RecallScreen sessionId={SESSION_ID} sessionSource="answer_session" />);
  emitVoiceEvent(finalTranscriptEvent);
  await waitFor(() => expect(mockSubmitVoiceResponse).toHaveBeenCalled());
});
```

#### Green: Minimal Implementation
**Files**:
- `frontend/src/components/RecallScreen.tsx`
- `frontend/src/api_contracts/sessionVoiceTurns.ts`

```tsx
if (sessionSource === 'session') {
  await updateSessionWorkingAnswer(sessionId, mergedAnswer, 'session');
} else {
  await submitVoiceResponse({ sessionId, transcript });
  await updateSessionWorkingAnswer(sessionId, mergedAnswer, 'answer_session');
}
```

#### Refactor: Improve Code
**File**:
- `frontend/src/components/RecallScreen.tsx`

```tsx
// Extract persistTranscriptBySource() helper to simplify event effect logic.
```

### Success Criteria
**Automated:**
- [x] Legacy-source and answer-source tests both fail first, then pass.
- [x] Existing move-on intent tests remain green.
- [x] `npm --prefix frontend run test -- src/components/__tests__/RecallScreen.voice.test.tsx`

**Manual:**
- [ ] Legacy session Recall no longer spams `/api/session/voice-response` failures.
- [ ] Saved status appears only when durable write succeeds.

---

## Behavior 3: Add Auth/Ownership Guard to Voice-Response Boundary

### Test Specification
**Given** `/api/session/voice-response` is called without auth  
**When** request arrives  
**Then** it returns 401 and does not run source-resolution logic.

**Given** caller is authenticated but not owner  
**When** session lookup occurs  
**Then** it returns unauthorized/not-found semantics without source-type disclosure.

### TDD Cycle

#### Red: Write Failing Tests
**Files**:
- `frontend/src/app/api/session/voice-response/__tests__/route.test.ts`
- `frontend/src/api_contracts/__tests__/submitVoiceResponse.test.ts`

```ts
it('returns 401 when Authorization header is missing');
it('submitVoiceResponse sends Authorization token from client auth context');
```

#### Green: Minimal Implementation
**Files**:
- `frontend/src/app/api/session/voice-response/route.ts`
- `frontend/src/api_contracts/submitVoiceResponse.ts`
- `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts`

```ts
// Route authenticates via AuthAndValidationFilter.
// Handler accepts auth user context and enforces ownership checks before detailed mismatch messaging.
```

#### Refactor: Improve Code
**Files**:
- `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts`

```ts
// Extract resolveAuthorizedVoiceSession() helper.
```

### Success Criteria
**Automated:**
- [x] Route auth tests fail first, then pass.
- [x] Client contract test confirms Authorization header behavior.
- [x] `npm --prefix frontend run test -- src/app/api/session/voice-response/__tests__/route.test.ts src/api_contracts/__tests__/submitVoiceResponse.test.ts`

**Manual:**
- [ ] Missing auth token returns clean auth error.
- [ ] Authorized session owner flow still works for answer-session transcripts.

---

## Behavior 4: Add Deterministic Mismatch Error Semantics (Post-Auth)

### Test Specification
**Given** `/api/session/voice-response` receives an ID missing from `answer_sessions` but present in owned `sessions`  
**When** handler resolves identity after auth/ownership gate  
**Then** it throws `INVALID_STATE` with explicit mismatch guidance.

**Edge Cases**
- Missing in both stores still returns not-found style message.
- Unsupported answer-session state still returns current state error.

### TDD Cycle

#### Red: Write Failing Tests
**Files**:
- `frontend/src/server/request_handlers/__tests__/ProcessVoiceResponseHandler.test.ts`
- `frontend/src/app/api/session/voice-response/__tests__/route.test.ts`

```ts
it('throws explicit mismatch message when owned id exists only in sessions', async () => {
  mockDAO.findAnswerSessionById.mockResolvedValue(null);
  mockDAO.findById.mockResolvedValue({ id: LEGACY_ID, state: 'initialized', ...timestamps });
  await expect(ProcessVoiceResponseHandler.handle(validPayload, authContext)).rejects.toMatchObject({
    code: 'INVALID_STATE',
    message: expect.stringContaining('prep/session workflow'),
  });
});
```

#### Green: Minimal Implementation
**File**:
- `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts`

```ts
// After auth+ownership checks:
// - if answer session missing and owned prep session exists -> explicit mismatch
// - if neither exists -> not found
```

#### Refactor: Improve Code
**File**:
- `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts`

```ts
// Keep mismatch/ownership branches isolated for maintainability.
```

### Success Criteria
**Automated:**
- [x] New mismatch case fails first, then passes.
- [x] Route returns 409 + mismatch message only in authorized context.
- [x] `npm --prefix frontend run test -- src/server/request_handlers/__tests__/ProcessVoiceResponseHandler.test.ts src/app/api/session/voice-response/__tests__/route.test.ts`

**Manual:**
- [ ] API consumers can distinguish wrong-source IDs from deleted/missing IDs when authorized.

---

## Behavior 5: Lock Dual-Workflow Regression Guards

### Test Specification
**Given** this fix intentionally keeps two workflows  
**When** start and finalize suites run  
**Then** start contracts stay `initialized`, active-session behavior stays intact, and finalize lifecycle remains `sessions`-based.

### TDD Cycle

#### Red: Add Explicit Assertions (only if missing)
**Files**:
- `frontend/src/app/api/session/start-default/__tests__/route.test.ts`
- `frontend/src/app/api/session/start-from-upload/__tests__/route.test.ts`
- `frontend/src/app/api/ingestion/url/__tests__/route.test.ts`
- `frontend/src/server/services/__tests__/ChannelIngestionPipelineAdapter.test.ts`
- `frontend/src/server/services/__tests__/FinalizeSessionService.validate.test.ts`

#### Green: Minimal Implementation
No functional changes expected in these paths.

#### Refactor: Improve Code
Add concise comments documenting that start/finalize are intentionally unchanged in this scope.

### Success Criteria
**Automated:**
- [x] Start route tests still assert `state: 'initialized'`.
- [x] Finalize validation tests remain green.
- [x] `npm --prefix frontend run test -- src/app/api/session/start-default/__tests__/route.test.ts src/app/api/session/start-from-upload/__tests__/route.test.ts src/app/api/ingestion/url/__tests__/route.test.ts src/server/services/__tests__/ChannelIngestionPipelineAdapter.test.ts src/server/services/__tests__/FinalizeSessionService.validate.test.ts`
- [x] Targeted sweep:
  - `npm --prefix frontend run test -- src/components/__tests__/RecallScreen.voice.test.tsx src/server/request_handlers/__tests__/ProcessVoiceResponseHandler.test.ts src/app/api/session/voice-response/__tests__/route.test.ts src/app/api/session/voice-turns/__tests__/route.test.ts src/modules/session/__tests__/SessionWorkflowShell.test.tsx src/modules/session/__tests__/stageMapper.test.ts`
- [ ] `npm --prefix frontend run type-check && npm --prefix frontend run lint`

**Manual:**
- [ ] Start from URL/default/upload and verify session opens as before.
- [ ] Record on legacy-loaded session no longer throws mismatch loop.
- [ ] For legacy source, write transcript then refresh and confirm read-back persists.

## Integration & E2E Testing
- Legacy source scenario:
  1. Create session from `/api/session/start-default` (returns `initialized`).
  2. Load `/session/:id`.
  3. Emit transcript.
  4. Verify no `/api/session/voice-response` request.
  5. Verify write via source-aware voice-turns call.
  6. Reload session and confirm read-back equals written content.
- Voice source scenario:
  1. Load a known `answer_session`-backed session.
  2. Emit transcript.
  3. Verify `/api/session/voice-response` is called and progression path succeeds.
- Explicit mismatch scenario:
  1. POST owned legacy `sessions.id` to `/api/session/voice-response` with valid auth.
  2. Verify `409 INVALID_STATE` with mismatch guidance.
- Unauthorized scenario:
  1. POST to `/api/session/voice-response` without auth.
  2. Verify 401 and no source-detail leakage.

## References
- Beads issue: `silmari-writer-bxt`
- Prior plan: `thoughts/searchable/shared/plans/2026-03-04--10-41--tdd-fix-voice-response-session-source-mismatch.md`
- Prior review: `thoughts/searchable/shared/plans/2026-03-04--10-41--tdd-fix-voice-response-session-source-mismatch-REVIEW.md`
- Contract-A predecessor: `thoughts/searchable/shared/plans/2026-03-04--11-54--tdd-fix-voice-response-session-source-mismatch-contract-a.md`
