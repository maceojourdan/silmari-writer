# PATH: recall-advancement-model

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from existing code — RecallScreen.tsx, recall/progress/route.ts, session/voice-turns/route.ts, recallQuestions.ts, SessionDAO.ts

## Purpose

Behavioral model of the recall question advancement state machine. Captures the decision chain from move-on intent detection through source-aware story record lookup, progress guard evaluation, to question advancement or blocking.

## Trigger

User utterance matching move-on intent pattern (`/next question|move on|skip this|let's continue|continue to next/`) during an active voice recall session.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | RecallScreen | UI component orchestrating the decision chain |
| `ui-y5t3` | RecallProgressLoader | Fetches progress from API |
| `db-d3w8` | SessionDAO | Story record lookup and question progress persistence |

## Steps

1. **DetectMoveOnIntent**
   - Input: Final transcript from voice model
   - Process: Regex match against move-on phrases
   - Output: Boolean intent detection
   - Error: None — pure function, always returns

2. **CheckAdvanceInFlight**
   - Input: `advanceInFlightRef.current`
   - Process: Mutex check
   - Output: If locked → blocked with reason `advance_in_flight`
   - Error: None

3. **EvaluateMoveOnAfterProgressRefresh**
   - Input: sessionId, sessionSource
   - Process: Awaits pending refresh or triggers new `loadRecallProgress()` call to `/api/recall/progress`
   - Output: Progress snapshot with `{ anchors, actions, outcomes, incompleteSlots }`
   - Error: On fetch failure → returns NEUTRAL_PROGRESS (all zeros)

4. **ResolveStoryRecordBySource** (inside progress API)
   - Input: sessionId, sessionSource
   - Process:
     - `sessionSource="session"` → `findStoryRecordByPrepSessionId(sessionId)` (queries `WHERE session_id = X`)
     - `sessionSource="answer_session"` → `findStoryRecordByVoiceSessionId(sessionId)` (queries `WHERE voice_session_id = X`)
   - Output: AnswerStoryRecord | null
   - Error: **BUG** — When record was created with `voice_session_id` but looked up via `session_id`, returns null

5. **ComputeRecallProgress**
   - Input: Story record content + responses corpus
   - Process: Regex pattern matching for anchors, actions, outcomes
   - Output: `{ anchors: N, actions: N, outcomes: N, incompleteSlots: [...] }`
   - Error: If story record is null → returns `{ 0, 0, 0, incompleteSlots: ['anchors', 'actions', 'outcomes'] }`

6. **GuardDecision**
   - Input: Progress snapshot from step 5
   - Process: `deriveIncompleteSlots(snapshot).length === 0`
   - Output: Boolean — advance allowed or blocked
   - Error: None

7. **AdvanceQuestionFlow** (if guard allows)
   - Input: Current questionProgress, questionSet
   - Process:
     1. Local: `advanceQuestionProgress()` → increments currentIndex, updates activeQuestionId
     2. Remote: POST `/api/session/voice-turns` with `action: 'advance_question'`
     3. Remote persists via `updateStoryRecordQuestionProgress()`
   - Output: New QuestionProgressState
   - Error: Remote failure non-blocking; local advancement still applies

## Terminal Condition

- **Advanced**: `currentIndex` incremented, new question displayed, coach prompt updated
- **All Complete**: `currentIndex >= total`, triggers `onAdvanceToReview()`
- **Blocked**: Stop controls shown, coach prompt suggests filling missing slots

## Feedback Loops

Blocked → ReturnToIdle → user speaks more → SlotsBecomeFilled → DetectMoveOnIntent → retry.
With the current bug, this loop never exits when source mismatch makes the record unfindable.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | currentIndex never decreases | recallQuestions.ts:85 | MonotonicProgress | `expect(after.currentIndex).toBeGreaterThanOrEqual(before.currentIndex)` |
| INV-2 | advanceInFlight only TRUE during advancing | RecallScreen.tsx:384-428 | AdvanceMutexSafety | `if (advanceInFlight) expect(pc).toBe("advancing")` |
| INV-3 | Blocked implies record-not-found OR slots-incomplete | RecallScreen.tsx:622-624 | ErrorConsistency | `if (blocked) expect(!found \|\| !complete).toBe(true)` |
| INV-4 | Guard allows when record found AND slots complete | RecallScreen.tsx:325-327 | GuardCorrectnessWhenFound | `if (found && complete) expect(guardAllows).toBe(true)` |
| INV-5 | Complete slots + questions remaining → eventually advance | RecallScreen.tsx full chain | SourceAwareAdvancement | `if (slotsComplete) expect(advanced).eventually.toBe(true)` |

## Change Impact Analysis

**Proposed change:** Two-part fix:
1. Use source-aware recall progress path — `resolveStoryRecordBySource` must find the record regardless of which column (`session_id` or `voice_session_id`) it was created with
2. Normalize question display from `activeQuestionId` when present, not only `currentIndex`

**Affected steps:** Step 4 (ResolveStoryRecordBySource), Step 6 (GuardDecision), Step 7 display

**Affected invariants:** INV-5 (SourceAwareAdvancement) — currently violated, fix should make it pass

**Risk:** Changing the lookup logic could surface previously-unseen story records, causing unexpected progress jumps if records have stale content

**Recommendation:**
1. Fix `resolveStoryRecordBySource` to try both columns (session_id, voice_session_id) as fallback
2. Add "force advance" path for "next question" intent that bypasses slot guard
3. Keep "move on" intent as guarded advance with slot check
