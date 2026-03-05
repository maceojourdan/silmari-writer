---- MODULE RecallAdvancement ----
\* Formal model of the recall question advancement state machine.
\*
\* Models the decision chain from move-on intent detection through
\* source-aware story record lookup, progress guard evaluation,
\* to question advancement or blocking.
\*
\* BUG MODELED: When sessionSource="session" but the story record
\* is linked only via voice_session_id (not session_id), the
\* resolveStoryRecordBySource lookup returns NULL, progress returns
\* all zeros, and the guard blocks advancement even when the user
\* has provided complete slot content.
\*
\* Source files:
\*   - frontend/src/components/RecallScreen.tsx
\*   - frontend/src/app/api/recall/progress/route.ts
\*   - frontend/src/app/api/session/voice-turns/route.ts
\*   - frontend/src/lib/recallQuestions.ts
\*   - frontend/src/server/data_access_objects/SessionDAO.ts

EXTENDS Naturals, FiniteSets

CONSTANTS
  NUM_QUESTIONS    \* Number of recall questions (e.g., 4)

VARIABLES
  pc,              \* Program counter / current state
  currentIndex,    \* Which question we are on (0-based)
  sessionSource,   \* How session was initiated: "session" | "answer_session"
  recordLinkMode,  \* How story record is linked in DB: "session_id" | "voice_session_id" | "both"
  slotsComplete,   \* Whether user provided enough content for all 3 slot types
  advanceInFlight, \* Mutex: is an advance operation currently running?
  storyRecordFound \* Whether the source-aware lookup found a story record

vars == <<pc, currentIndex, sessionSource, recordLinkMode, slotsComplete, advanceInFlight, storyRecordFound>>

\* -----------------------------------------------------------------------
\* Type domains
\* -----------------------------------------------------------------------

PcStates == {
  "idle",               \* Waiting for voice input or user action
  "move_on_detected",   \* Move-on intent detected in transcript
  "checking_progress",  \* Progress fetched, evaluating guard
  "blocked",            \* Guard blocked advancement
  "advancing",          \* Advancing question (local + remote)
  "advanced",           \* Question successfully advanced
  "all_complete"        \* All questions finished
}

SessionSources == {"session", "answer_session"}

RecordLinkModes == {"session_id", "voice_session_id", "both"}

\* -----------------------------------------------------------------------
\* Story record resolution (models current buggy DB lookup)
\* -----------------------------------------------------------------------
\*
\* sessionSource="session"        -> queries WHERE session_id = X
\* sessionSource="answer_session" -> queries WHERE voice_session_id = X
\*
\* If the record was created with only the OTHER column populated,
\* the lookup misses it and returns NULL.

ResolveStoryRecord(source, linkMode) ==
  CASE source = "session" /\ linkMode = "session_id"         -> TRUE
    [] source = "session" /\ linkMode = "both"               -> TRUE
    [] source = "session" /\ linkMode = "voice_session_id"   -> FALSE
    [] source = "answer_session" /\ linkMode = "voice_session_id" -> TRUE
    [] source = "answer_session" /\ linkMode = "both"        -> TRUE
    [] source = "answer_session" /\ linkMode = "session_id"  -> FALSE

\* -----------------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------------

Init ==
  /\ pc = "idle"
  /\ currentIndex = 0
  /\ sessionSource \in SessionSources
  /\ recordLinkMode \in RecordLinkModes
  /\ slotsComplete \in BOOLEAN
  /\ advanceInFlight = FALSE
  /\ storyRecordFound = FALSE

\* -----------------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------------

\* User says "next question", "move on", "let's continue", etc.
\* Maps to: detectMoveOnIntent() in RecallScreen.tsx:112
DetectMoveOnIntent ==
  /\ pc = "idle"
  /\ currentIndex < NUM_QUESTIONS
  /\ ~advanceInFlight
  /\ pc' = "move_on_detected"
  /\ UNCHANGED <<currentIndex, sessionSource, recordLinkMode, slotsComplete, advanceInFlight, storyRecordFound>>

\* Fetch /api/recall/progress and resolve story record by source.
\* Maps to: evaluateMoveOnAfterProgressRefresh() -> loadRecallProgress()
\*          -> resolveStoryRecordBySource() in recall/progress/route.ts:60
CheckProgress ==
  /\ pc = "move_on_detected"
  /\ storyRecordFound' = ResolveStoryRecord(sessionSource, recordLinkMode)
  /\ pc' = "checking_progress"
  /\ UNCHANGED <<currentIndex, sessionSource, recordLinkMode, slotsComplete, advanceInFlight>>

\* Guard allows advancement: record found AND all slots complete.
\* Maps to: shouldAdvanceFromMoveOnIntent() in RecallScreen.tsx:325
\*          checking deriveIncompleteSlots().length === 0
GuardAllows ==
  /\ pc = "checking_progress"
  /\ storyRecordFound
  /\ slotsComplete
  /\ pc' = "advancing"
  /\ advanceInFlight' = TRUE
  /\ UNCHANGED <<currentIndex, sessionSource, recordLinkMode, slotsComplete, storyRecordFound>>

\* Guard blocks: record not found OR slots incomplete.
GuardBlocks ==
  /\ pc = "checking_progress"
  /\ (~storyRecordFound \/ ~slotsComplete)
  /\ pc' = "blocked"
  /\ UNCHANGED <<currentIndex, sessionSource, recordLinkMode, slotsComplete, advanceInFlight, storyRecordFound>>

\* Execute question advancement (local advanceQuestionProgress + remote persist).
\* Maps to: advanceQuestionFlow() in RecallScreen.tsx:382
\*          -> advanceQuestionProgress() in recallQuestions.ts:81
\*          -> advanceSessionQuestion() -> POST /api/session/voice-turns
AdvanceQuestion ==
  /\ pc = "advancing"
  /\ currentIndex' = currentIndex + 1
  /\ advanceInFlight' = FALSE
  /\ pc' = IF currentIndex + 1 >= NUM_QUESTIONS
            THEN "all_complete"
            ELSE "advanced"
  /\ UNCHANGED <<sessionSource, recordLinkMode, slotsComplete, storyRecordFound>>

\* Return to idle after blocked or advanced states.
ReturnToIdle ==
  /\ pc \in {"blocked", "advanced"}
  /\ pc' = "idle"
  /\ UNCHANGED <<currentIndex, sessionSource, recordLinkMode, slotsComplete, advanceInFlight, storyRecordFound>>

\* Terminal: all questions completed, system is done.
Done ==
  /\ pc = "all_complete"
  /\ UNCHANGED vars

\* User continues speaking, filling remaining slots.
\* Models: user provides anchors/actions/outcomes content over time.
SlotsBecomeFilled ==
  /\ pc = "idle"
  /\ ~slotsComplete
  /\ slotsComplete' = TRUE
  /\ UNCHANGED <<pc, currentIndex, sessionSource, recordLinkMode, advanceInFlight, storyRecordFound>>

\* -----------------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------------

Next ==
  \/ DetectMoveOnIntent
  \/ CheckProgress
  \/ GuardAllows
  \/ GuardBlocks
  \/ AdvanceQuestion
  \/ ReturnToIdle
  \/ SlotsBecomeFilled
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -----------------------------------------------------------------------
\* Baseline Properties
\* -----------------------------------------------------------------------

\* INV: State variables remain within valid domains.
TypeInvariant ==
  /\ pc \in PcStates
  /\ currentIndex \in 0..NUM_QUESTIONS
  /\ sessionSource \in SessionSources
  /\ recordLinkMode \in RecordLinkModes
  /\ slotsComplete \in BOOLEAN
  /\ advanceInFlight \in BOOLEAN
  /\ storyRecordFound \in BOOLEAN

\* INV: Blocked state implies a specific blocking reason.
ErrorConsistency ==
  pc = "blocked" => (~storyRecordFound \/ ~slotsComplete)

\* TEMPORAL: Every run eventually reaches a terminal or intermediate milestone.
Reachability == <>(pc \in {"all_complete", "blocked", "advanced"})

\* -----------------------------------------------------------------------
\* Domain-Specific Properties
\* -----------------------------------------------------------------------

\* INV: currentIndex never decreases.
MonotonicProgress == [][currentIndex' >= currentIndex]_currentIndex

\* INV: advanceInFlight is only TRUE while actively advancing.
AdvanceMutexSafety ==
  advanceInFlight => pc = "advancing"

\* TEMPORAL / BUG DETECTION:
\* "If slots are complete and there are questions remaining,
\*  the system should eventually advance."
\*
\* EXPECTED: VIOLATED in the buggy model.
\* Counterexample: sessionSource="session", recordLinkMode="voice_session_id",
\* slotsComplete=TRUE -> resolveStoryRecord returns FALSE -> blocked forever.
\*
\* This property demonstrates the source-mismatch bug:
\* the user has filled all slots but the system never advances
\* because the DB lookup uses the wrong column.
SourceAwareAdvancement ==
  [](slotsComplete /\ currentIndex < NUM_QUESTIONS => <>(pc \in {"advanced", "all_complete"}))

\* INV: When story record IS found and slots ARE complete,
\* the guard must allow (not block).
\* This is the positive contract the fix must preserve.
GuardCorrectnessWhenFound ==
  (pc = "checking_progress" /\ storyRecordFound /\ slotsComplete) => pc' # "blocked"

====
