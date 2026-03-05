---- MODULE RecallAdvancementFixed ----
\* Post-fix model of the recall question advancement state machine.
\*
\* Models the PATCHED behavior where resolveStoryRecordBySource uses
\* findStoryRecordByCanonicalSessionId — a fallback chain that tries
\* the preferred column first, then the alternate column.
\*
\* Patch: SessionDAO.findStoryRecordByCanonicalSessionId(sessionId, preferredSource)
\*   preferredSource="session"        -> try session_id THEN voice_session_id
\*   preferredSource="answer_session" -> try voice_session_id THEN session_id
\*
\* Both route.ts files (voice-turns, recall/progress) now delegate to
\* this canonical resolver instead of hard-forking on sessionSource.
\*
\* EXPECTED: All properties that were VIOLATED in the buggy model
\*           (SourceAwareAdvancement, Reachability) should now PASS.
\*
\* Source files (patched):
\*   - frontend/src/server/data_access_objects/SessionDAO.ts
\*   - frontend/src/app/api/session/voice-turns/route.ts
\*   - frontend/src/app/api/recall/progress/route.ts

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
  storyRecordFound \* Whether the canonical lookup found a story record

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
\* Story record resolution (FIXED: canonical fallback chain)
\* -----------------------------------------------------------------------
\*
\* findStoryRecordByCanonicalSessionId(sessionId, preferredSource):
\*   1. Try preferred column (session_id or voice_session_id)
\*   2. If not found, try the alternate column
\*   3. Return first hit or null
\*
\* This means: as long as the record exists under ANY column,
\* the lookup succeeds regardless of sessionSource.

ResolveStoryRecordFixed(source, linkMode) ==
  \* Record linked by session_id: found by session preferred OR answer_session fallback
  \* Record linked by voice_session_id: found by answer_session preferred OR session fallback
  \* Record linked by both: always found
  CASE linkMode = "both"               -> TRUE
    [] linkMode = "session_id"         -> TRUE  \* session: primary hit; answer_session: fallback hit
    [] linkMode = "voice_session_id"   -> TRUE  \* answer_session: primary hit; session: fallback hit

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
\* Actions (identical to buggy model except CheckProgress uses fixed resolver)
\* -----------------------------------------------------------------------

\* User says "next question", "move on", "let's continue", etc.
DetectMoveOnIntent ==
  /\ pc = "idle"
  /\ currentIndex < NUM_QUESTIONS
  /\ ~advanceInFlight
  /\ pc' = "move_on_detected"
  /\ UNCHANGED <<currentIndex, sessionSource, recordLinkMode, slotsComplete, advanceInFlight, storyRecordFound>>

\* Fetch /api/recall/progress using FIXED canonical resolver.
\* Maps to: resolveStoryRecordBySource() now delegates to
\*          SessionDAO.findStoryRecordByCanonicalSessionId()
CheckProgress ==
  /\ pc = "move_on_detected"
  /\ storyRecordFound' = ResolveStoryRecordFixed(sessionSource, recordLinkMode)
  /\ pc' = "checking_progress"
  /\ UNCHANGED <<currentIndex, sessionSource, recordLinkMode, slotsComplete, advanceInFlight>>

\* Guard allows advancement: record found AND all slots complete.
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

\* Execute question advancement.
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

\* TEMPORAL / BUG FIX VERIFICATION:
\* "If slots are complete and there are questions remaining,
\*  the system should eventually advance."
\*
\* EXPECTED: PASSES in the fixed model.
\* With canonical fallback lookup, storyRecordFound is always TRUE
\* (regardless of linkMode), so the only remaining guard is slotsComplete.
\* When slotsComplete=TRUE, the guard allows and question advances.
SourceAwareAdvancement ==
  [](slotsComplete /\ currentIndex < NUM_QUESTIONS => <>(pc \in {"advanced", "all_complete"}))

\* NEW: With the fix, blocked can ONLY happen when slots are genuinely incomplete.
\* The source-mismatch path is eliminated.
BlockedOnlyFromIncompleteSlots ==
  pc = "blocked" => ~slotsComplete

====
