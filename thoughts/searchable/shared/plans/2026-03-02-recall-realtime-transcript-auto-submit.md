# Recall Realtime Transcript Auto-Submit Implementation Plan

## Overview
Wire the Recall voice session to automatically persist finalized spoken transcripts to `/api/session/voice-response`, with dedupe/in-flight protection and visible UI status. Keep first-utterance progression working immediately under the current backend (`INIT`-only), and define a follow-on backend phase to enable continuous multi-turn auto-progression.

## Current State Analysis

The realtime connection exists, but Recall does not consume transcript events or submit them into the session progression pipeline.

### Key Discoveries
- `RecallScreen` connects/disconnects realtime voice but never registers `setOnEvent` and never calls `submitVoiceResponse`: `frontend/src/components/RecallScreen.tsx:51`.
- `useRealtimeSession` already exposes `setOnEvent`, forwarding all data channel events from `createVoiceSession`: `frontend/src/hooks/useRealtimeSession.ts:17`, `frontend/src/hooks/useRealtimeSession.ts:50`, `frontend/src/lib/voice-session.ts:162`.
- The typed progression API contract already exists (`submitVoiceResponse`) and returns updated `session` + `storyRecord`: `frontend/src/api_contracts/submitVoiceResponse.ts:44`.
- `ProcessVoiceResponseHandler` currently rejects any state other than `INIT`: `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts:63`.
- `VoiceResponseProcessor` only defines a real transition for `INIT -> IN_PROGRESS`; other states return same state: `frontend/src/server/processors/VoiceResponseProcessor.ts:42`.
- `SessionWorkflowShell` derives stage once from initial `session` and keeps its own local stage; it does not react to updated `session` props after mount: `frontend/src/modules/session/SessionWorkflowShell.tsx:45`, `frontend/src/modules/session/SessionWorkflowShell.tsx:53`.
- `WritingFlowModule` currently passes only `selectedStory` to `RecallScreen`, so `sessionId` is not available at Recall level: `frontend/src/modules/WritingFlowModule.tsx:159`.

## Desired End State

A user can click Record in Recall, speak, and have each finalized utterance auto-submitted to session progression (starting with first utterance under current backend constraints), with clear UI status and synchronized session shell state.

### End-State Behaviors
- Realtime final transcript events trigger automatic POST to `/api/session/voice-response` with `{ sessionId, transcript }`.
- Partial/delta events never submit.
- Duplicate final events for the same utterance submit at most once.
- While a submission is in flight, additional events are guarded to prevent duplicate writes.
- UI reflects status transitions: listening, submitting, saved, error.
- On success, shell state is refreshed from server so route-level workflow state remains accurate.

## What We're NOT Doing
- Changing the realtime SDP proxy architecture or moving OpenAI auth client-side.
- Redesigning Recall UX beyond minimal status messaging required for this integration.
- Implementing speculative/multi-queue transcript batching in the first pass.
- Enabling continuous multi-turn progression in backend within Phase 1/2 (covered as explicit follow-on Phase 3).

## Implementation Approach

Implement in two delivery tracks:
1. **Frontend integration (Phase 1 + Phase 2):** ship immediate user value for first utterance progression with robust event handling and session refresh.
2. **Backend progression extension (Phase 3):** broaden accepted states and progression rules for continuous loop behavior.

The frontend track is safe to ship independently and is compatible with current backend constraints.

---

## Phase 1: Realtime Final Transcript -> Auto Submit in RecallScreen

### Overview
Add event consumption in `RecallScreen`, detect final user transcript events, auto-submit via existing API contract, and expose submission statuses.

### Changes Required

#### 1. Add final-transcript extraction utility
**File**: `frontend/src/lib/realtime-transcript.ts` (new)
**Changes**:
- Add a typed helper to parse realtime events and return normalized final transcript payload.
- Accept only final transcript event types (no partials). Primary target event:
  - `conversation.item.input_audio_transcription.completed`
- Normalize transcript text via trim and empty-check.
- Emit deterministic dedupe key (prefer event `item_id`, fallback hash of normalized text + timestamp token).

```ts
export interface FinalTranscriptEvent {
  dedupeKey: string;
  transcript: string;
}

export function extractFinalTranscriptEvent(event: { type: string; [k: string]: unknown }): FinalTranscriptEvent | null {
  if (event.type !== 'conversation.item.input_audio_transcription.completed') return null;
  const transcript = typeof event.transcript === 'string' ? event.transcript.trim() : '';
  if (!transcript) return null;
  const itemId = typeof event.item_id === 'string' ? event.item_id : null;
  return {
    dedupeKey: itemId ?? `text:${transcript.toLowerCase()}`,
    transcript,
  };
}
```

#### 2. Wire `setOnEvent` in RecallScreen
**File**: `frontend/src/components/RecallScreen.tsx`
**Changes**:
- Extend props with `sessionId?: string` and `onVoiceResponseSaved?: () => Promise<void> | void`.
- Import and call `submitVoiceResponse`.
- Register `setOnEvent` in `useEffect` and clear on cleanup.
- Add refs/state for dedupe and in-flight protection:
  - `submittedKeysRef: Set<string>`
  - `isSubmittingRef`
  - `lastSavedTranscriptRef`
- Ignore events when not connected or no `sessionId`.
- On extracted final transcript:
  - Skip if dedupe key already submitted.
  - Skip if in-flight (guard behavior for Phase 1 due INIT-only backend).
  - Set UI status to `submitting`, call `submitVoiceResponse`, then set `saved` or `error`.
  - On success, invoke `onVoiceResponseSaved` callback.

#### 3. Add UI status model
**File**: `frontend/src/components/RecallScreen.tsx`
**Changes**:
- Add explicit submit status state:
  - `'idle' | 'listening' | 'submitting' | 'saved' | 'error'`
- Render user-facing status text near existing voice status with dedicated test id.
- Preserve existing connect failure error (`voice-model-error`).

Example text behavior:
- Connected + waiting: `Listening for your response...`
- In-flight: `Saving your response...`
- Success: `Response saved.`
- Error: `Could not save response. Please try speaking again.`

#### 4. Extend RecallScreen unit tests
**File**: `frontend/src/components/__tests__/RecallScreen.voice.test.tsx`
**Changes**:
- Expand mocked `useRealtimeSession` to include `setOnEvent`.
- Add tests for:
  - registration/cleanup of `setOnEvent`
  - final transcript event triggers `submitVoiceResponse`
  - partial/non-final events do not trigger submit
  - duplicate final events submit once (dedupe)
  - in-flight guard prevents double submit
  - status text transitions (`listening` -> `submitting` -> `saved` / `error`)

#### 5. Add extractor unit tests
**File**: `frontend/src/lib/__tests__/realtime-transcript.test.ts` (new)
**Changes**:
- Validate extraction behavior, empty transcript rejection, and dedupe key generation.

### Success Criteria

#### Automated Verification
- [x] `npm --prefix frontend run test -- src/components/__tests__/RecallScreen.voice.test.tsx`
- [x] `npm --prefix frontend run test -- src/lib/__tests__/realtime-transcript.test.ts`
- [ ] `npm --prefix frontend run type-check`
- [ ] `npm --prefix frontend run lint`

#### Manual Verification
- [ ] Open `/session/{id}` in Recall stage, click Record, speak one utterance, wait for silence.
- [ ] Confirm status changes to listening then saving then saved.
- [ ] Confirm network call to `/api/session/voice-response` contains current `sessionId` + transcript.
- [ ] Confirm repeated delivery of same final event does not create duplicate submissions.

---

## Phase 2: Thread Session Context and Sync Session Shell State

### Overview
Pass `sessionId` into Recall flow and ensure shell/session state updates after successful auto-submit.

### Changes Required

#### 1. Propagate `sessionId` into RecallScreen
**Files**:
- `frontend/src/modules/session/SessionWorkflowShell.tsx`
- `frontend/src/modules/WritingFlowModule.tsx`
- `frontend/src/components/RecallScreen.tsx`

**Changes**:
- Add optional `sessionId` prop to `WritingFlowModule` and `RecallScreen`.
- Pass `session.id` from `SessionWorkflowShell` down to Recall.

#### 2. Add refresh callback from route shell
**Files**:
- `frontend/src/app/session/[sessionId]/page.tsx`
- `frontend/src/modules/session/SessionWorkflowShell.tsx`
- `frontend/src/modules/WritingFlowModule.tsx`

**Changes**:
- In `SessionPage`, add `refreshSession` callback that re-runs `getSession(sessionId)` and updates local `session` state.
- Pass callback down (`onVoiceResponseSaved` chain) to Recall.
- Invoke callback after successful `submitVoiceResponse` so shell is synchronized.

#### 3. Make SessionWorkflowShell reactive to updated session prop
**File**: `frontend/src/modules/session/SessionWorkflowShell.tsx`
**Changes**:
- Add `useEffect` to recompute stage when `session.state/source/questionId` props change.
- Keep existing user-driven transitions (`transitionTo`) but allow authoritative server refresh to realign shell stage.

```ts
useEffect(() => {
  setStage(mapSessionStateToStage(session.state, {
    source: session.source,
    questionId: session.questionId ?? null,
  }));
}, [session.state, session.source, session.questionId]);
```

#### 4. Extend session shell tests
**Files**:
- `frontend/src/modules/session/__tests__/SessionWorkflowShell.test.tsx`
- `frontend/src/app/session/[sessionId]/__tests__/page.flow.integration.test.tsx` (if needed)

**Changes**:
- Add rerender-based test proving shell stage updates when session prop changes.
- Add callback wiring test ensuring successful Recall submit path triggers refresh function.

### Success Criteria

#### Automated Verification
- [x] `npm --prefix frontend run test -- src/modules/session/__tests__/SessionWorkflowShell.test.tsx`
- [x] `npm --prefix frontend run test -- src/app/session/[sessionId]/__tests__/page.flow.integration.test.tsx`
- [ ] `npm --prefix frontend run type-check`

#### Manual Verification
- [ ] After first voice submit success, refresh-free UI remains consistent with server session state.
- [ ] No regression in Review <-> Recall navigation.
- [ ] Reloading `/session/{id}` after submit shows same progressed state.

---

## Phase 3: Backend Extension for Continuous Multi-Turn Voice Loop (Follow-on)

### Overview
Remove `INIT`-only restriction and define progression logic for additional states so repeated final transcripts can continuously advance the recall loop.

### Changes Required

#### 1. Expand valid input states in handler
**File**: `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts`
**Changes**:
- Replace strict `session.state !== 'INIT'` guard with allowlist (for example `INIT`, `IN_PROGRESS`, `RECALL`).
- Keep explicit invalid-state error for unsupported states (`COMPLETE`, `VERIFY`, terminal states).

#### 2. Define multi-state progression rules
**File**: `frontend/src/server/processors/VoiceResponseProcessor.ts`
**Changes**:
- Add explicit transitions for allowed loop states.
- Ensure returned nextState always satisfies `VALID_STATE_TRANSITIONS` from `AnswerSession`.

Potential initial rule set:
- `INIT -> IN_PROGRESS`
- `IN_PROGRESS -> RECALL`
- `RECALL -> COMPLETE`

#### 3. Harden service/handler tests
**Files**:
- `frontend/src/server/request_handlers/__tests__/ProcessVoiceResponseHandler.test.ts`
- `frontend/src/__tests__/processVoiceInput.integration.test.ts`
- `frontend/src/server/processors/__tests__/VoiceResponseProcessor.test.ts`

**Changes**:
- Replace INIT-only assertions with allowlist/transition assertions.
- Add tests for multiple sequential submissions and invalid terminal-state submissions.

#### 4. Confirm stage mapping remains correct
**Files**:
- `frontend/src/modules/session/stageMapper.ts`
- `frontend/src/modules/session/__tests__/SessionWorkflowShell.test.tsx`

**Changes**:
- Verify mapped UI behavior for new progression sequence still lands in `RECALL_REVIEW` until draft/finalize boundaries.

### Success Criteria

#### Automated Verification
- [x] `npm --prefix frontend run test -- src/server/request_handlers/__tests__/ProcessVoiceResponseHandler.test.ts`
- [x] `npm --prefix frontend run test -- src/server/processors/__tests__/VoiceResponseProcessor.test.ts`
- [x] `npm --prefix frontend run test -- src/__tests__/processVoiceInput.integration.test.ts`
- [ ] `npm --prefix frontend run type-check`

#### Manual Verification
- [ ] Speak multiple utterances in one Recall session; each final transcript persists once.
- [ ] Session progresses across intended intermediate states without manual text entry.
- [ ] Terminal/invalid states reject new voice responses with clear error surface.

---

## Testing Strategy

### Unit Tests
- Transcript extractor parsing and dedupe key behavior.
- RecallScreen event handling (final-only, dedupe, in-flight).
- SessionWorkflowShell reactivity to refreshed session props.

### Integration Tests
- `/session/[sessionId]` route hydration + shell rendering.
- Voice response processing path (`ProcessVoiceResponseHandler` integration test).

### Manual Testing Steps
1. Start session from `/writer` and land on `/session/{sessionId}`.
2. Enter Recall, click Record, speak one utterance, wait for final transcript.
3. Verify auto-submit call and saved status.
4. Speak again (after Phase 3) and confirm next turn persists and progresses.
5. Force backend error (invalid state) and verify UI shows recoverable error status.

## Performance Considerations
- Event handler must avoid repeated React re-renders for high-frequency realtime events; use refs for dedupe/in-flight state.
- Only final transcript events should trigger network I/O.
- Session refresh callback should be invoked only on successful save to avoid unnecessary refetches.

## Migration Notes
- No schema migration is required for Phase 1/2.
- Phase 3 changes business logic only (state-acceptance/progression rules); ensure test fixtures and docs are updated in lockstep.

## Beads Tracking
- Primary issue: `silmari-writer-8b1` (closed)

## References
- `frontend/src/components/RecallScreen.tsx`
- `frontend/src/hooks/useRealtimeSession.ts`
- `frontend/src/lib/voice-session.ts`
- `frontend/src/api_contracts/submitVoiceResponse.ts`
- `frontend/src/server/request_handlers/ProcessVoiceResponseHandler.ts`
- `frontend/src/server/processors/VoiceResponseProcessor.ts`
- `frontend/src/modules/session/SessionWorkflowShell.tsx`
- `frontend/src/modules/WritingFlowModule.tsx`
- `frontend/src/app/session/[sessionId]/page.tsx`
- `specs/voice-loop.md`
- `specs/ARCHITECTURE.md`
