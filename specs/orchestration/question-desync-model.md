# PATH: question-desync-model

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from existing code — RecallScreen.tsx, recallQuestions.ts, voice-turns/route.ts, useRealtimeSession.ts

## Purpose

Behavioral model of the three-actor question state desync bug where UI, backend, and LLM hold independent copies of `questionProgress`. When a user advances questions while the voice session remains connected (move-on intent path), the LLM continues coaching the previous question because its instructions are set once at `connect()` and never updated.

## Trigger

User says "next question" (move-on intent detected) during active voice session, then clicks the "Next question" button while the realtime voice session remains connected.

## Steps

1. **VoiceConnect**
   - Input: User clicks Record, `activeQuestion` resolved from `questionProgress`
   - Process: `connect(VOICE_MODES.VOICE_EDIT, { instructions: buildRecallInstructions(selectedStory, activeQuestion.text) })`
   - Output: `connected=TRUE`, `llmIndex=uiIndex`
   - Error: Connection failure → voice error state

2. **DetectMoveOn**
   - Input: Final transcript event from realtime session
   - Process: `detectMoveOnIntent(transcript)` matches "next question|move on|..."
   - Output: `stopControlsVisible=TRUE`, voice session **stays connected**
   - Error: None — always succeeds if pattern matches

3. **AdvanceWhileConnected (THE BUG)**
   - Input: User clicks "Next question" button from stop controls
   - Process: `advanceQuestionFlow()` — sets `questionProgress` locally, calls `advanceSessionQuestion()` API
   - Output: `uiIndex++`, `dbIndex++` (or stale on failure), **`llmIndex` UNCHANGED**
   - Error: Backend call can fail silently (try/catch with "Non-blocking" comment)

4. **Return to Listening (DESYNCED)**
   - Input: `advanceQuestionFlow` completes, `connected` still TRUE
   - Process: Component re-renders with new `activeQuestion` text in UI, old instructions in LLM
   - Output: UI shows Q(N+1), coach prompt shows Q(N+1), LLM coaches Q(N)
   - Error: Feedback loop — user hears Q(N) coaching, sees Q(N+1), gets confused

## Terminal Condition

`FinishToReview` — user clicks "Finish to Review" on last question. Disconnects voice session, sets `pc="all_complete"`.

## Feedback Loops

**Desync feedback loop (the bug):**
listening → DetectMoveOn → stop_presented → AdvanceWhileConnected → listening (desynced)
Each iteration deepens the gap between `uiIndex` and `llmIndex`.

**Safe path (manual stop):**
listening → ManualStop (disconnects) → stop_presented → AdvanceWhileDisconnected → idle → VoiceConnect (fresh instructions)

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | Connected implies LLM has valid question | RecallScreen.tsx:399 | ErrorConsistency | `expect(llmIndex).toBeGreaterThanOrEqual(0)` when connected |
| INV-2 | UI and LLM agree while listening | RecallScreen.tsx:317-345 | NoSilentDesync | `expect(uiIndex).toBe(llmIndex)` when connected and listening |
| INV-3 | Full triple sync when DB is current | RecallScreen.tsx:326 | FullTripleSync | After successful backend call, all three indices match |
| INV-4 | UI never behind LLM | RecallScreen.tsx:321 | UINotBehindLLM | `expect(uiIndex).toBeGreaterThanOrEqual(llmIndex)` |
| INV-5 | UI index monotonically increasing | RecallScreen.tsx:319 | MonotonicProgress | `expect(newIndex).toBeGreaterThanOrEqual(oldIndex)` |
| INV-6 | Desync eventually resolves | — | LLMEventualResync | After advance, either LLM syncs or disconnects |

## Change Impact Analysis

**Proposed change:** Add LLM instruction sync to `advanceQuestionFlow` when voice session is connected.

**Two fix options:**
1. **Disconnect + reconnect:** Call `disconnect()` then `connect()` with new `buildRecallInstructions(selectedStory, nextQuestion.text)` inside `advanceQuestionFlow`
2. **Session.update via sendEvent:** Call `sendEvent({ type: 'session.update', session: { instructions: newInstructions } })` to update LLM instructions without breaking the connection

**Affected steps:** Step 3 (AdvanceWhileConnected) — must add LLM resync effect
**Affected invariants:** INV-2, INV-3, INV-6 — currently violated, fix makes them hold
**Risk:** Option 1 (reconnect) briefly drops audio; Option 2 (session.update) is seamless but depends on OpenAI Realtime API supporting mid-session instruction updates
**Recommendation:** Option 2 (sendEvent session.update) preferred for UX continuity; fall back to Option 1 if session.update is not supported

## TLC Verification Results

**Buggy model (FIX_ENABLED=FALSE):**
- NoSilentDesync: **VIOLATED** — counterexample in 4 states
- 6 states generated, 5 distinct (stopped early at first violation)

**Fixed model (FIX_ENABLED=TRUE):**
- All 8 properties: **PASSED**
- 106 states generated, 45 distinct, complete state space explored

**Counterexample (buggy):**
```
State 1: idle, connected=FALSE, llmIndex=-1
State 2: VoiceConnect → listening, connected=TRUE, llmIndex=0, uiIndex=0
State 3: DetectMoveOn → stop_presented (voice still connected)
State 4: AdvanceWhileConnected → listening, uiIndex=1, dbIndex=1, llmIndex=0 ← DESYNC
```
