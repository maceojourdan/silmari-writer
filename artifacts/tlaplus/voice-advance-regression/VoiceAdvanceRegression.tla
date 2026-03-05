---- MODULE VoiceAdvanceRegression ----
(***************************************************************************)
(* Models the voice advance regression bug observed in HAR trace           *)
(* session 7d14f077-84b7-47d3-97f5-c24ba8db317e (2026-03-05).            *)
(*                                                                         *)
(* Four-actor state model:                                                 *)
(*   1. UI (React state) — uiIndex                                        *)
(*   2. LLM (realtime session) — llmIndex + llmSpeaking                   *)
(*   3. Backend advance path — advIndex (advance_question endpoint)        *)
(*   4. Backend upsert path — upsertIndex (update_working_answer for      *)
(*      session source via upsertPrepStoryRecordWorkingAnswer)             *)
(*                                                                         *)
(* BUG 1 (Backend Record Divergence):                                      *)
(*   advance_question resolves story record via                            *)
(*   findStoryRecordByCanonicalSessionId and updates question_progress.    *)
(*   update_working_answer (session source) resolves via                   *)
(*   upsertPrepStoryRecordWorkingAnswer which can find a DIFFERENT         *)
(*   record or INSERT a new one with default progress (currentIndex=0).    *)
(*   HAR proof: advance_question returns index=1, next                     *)
(*   update_working_answer returns index=0.                                *)
(*                                                                         *)
(* BUG 2 (LLM Silence After session.update):                              *)
(*   After advanceQuestionFlow sends session.update with new instructions, *)
(*   the LLM does not auto-speak. It waits for user input before           *)
(*   responding, creating a silence gap where the user must prompt.        *)
(*                                                                         *)
(* BUG 3 (UI Regression on Refetch):                                       *)
(*   If the UI refetches from the diverged backend (page reload, effect    *)
(*   re-run), it adopts the regressed upsertIndex, losing the advance.    *)
(*                                                                         *)
(* FIX_RECORD enables unified record resolution.                           *)
(* FIX_REPROMPT enables LLM auto-speak after session.update.              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    MAX_Q,              \* Number of questions (e.g. 4)
    FIX_RECORD,         \* TRUE = both paths resolve same record
    FIX_REPROMPT        \* TRUE = send response.create after session.update

VARIABLES
    uiIndex,            \* 0..MAX_Q: question index the UI displays
    advIndex,           \* 0..MAX_Q: index in record that advance_question writes
    upsertIndex,        \* 0..MAX_Q: index in record that update_working_answer reads
    llmIndex,           \* -1..MAX_Q: question baked into LLM instructions
    llmSpeaking,        \* BOOLEAN: whether LLM is actively producing audio
    connected,          \* BOOLEAN: realtime voice session active
    userSpoke,          \* BOOLEAN: user has spoken since last advance
    stopVisible,        \* BOOLEAN: stop controls shown
    pc                  \* component state

vars == <<uiIndex, advIndex, upsertIndex, llmIndex, llmSpeaking, connected, userSpoke, stopVisible, pc>>

TypeInvariant ==
    /\ uiIndex \in 0..MAX_Q
    /\ advIndex \in 0..MAX_Q
    /\ upsertIndex \in 0..MAX_Q
    /\ llmIndex \in -1..MAX_Q
    /\ llmSpeaking \in BOOLEAN
    /\ connected \in BOOLEAN
    /\ userSpoke \in BOOLEAN
    /\ stopVisible \in BOOLEAN
    /\ pc \in {"idle", "listening", "stop_presented", "advancing",
               "correction", "all_complete"}

Init ==
    /\ uiIndex = 0
    /\ advIndex = 0
    /\ upsertIndex = 0
    /\ llmIndex = -1
    /\ llmSpeaking = FALSE
    /\ connected = FALSE
    /\ userSpoke = FALSE
    /\ stopVisible = FALSE
    /\ pc = "idle"

(* ===================================================================== *)
(* TRANSITIONS                                                            *)
(* ===================================================================== *)

\* User clicks Record — voice session connects, LLM starts greeting
\* Source: RecallScreen.tsx:395-422 (handleRecord)
VoiceConnect ==
    /\ pc = "idle"
    /\ uiIndex < MAX_Q
    /\ connected' = TRUE
    /\ llmIndex' = uiIndex
    /\ llmSpeaking' = TRUE          \* LLM auto-greets on initial connect
    /\ userSpoke' = FALSE
    /\ pc' = "listening"
    /\ UNCHANGED <<uiIndex, advIndex, upsertIndex, stopVisible>>

\* User speaks — transcript captured and persisted
\* Source: RecallScreen.tsx:515-584 (event handler)
\* This calls update_working_answer which goes through upsert path
UserSpeaks ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ userSpoke' = TRUE
    /\ llmSpeaking' = TRUE           \* LLM responds to user speech
    \* Backend upsert path returns its index (may differ from advIndex)
    \* When FIX_RECORD is enabled, upsert path reads the same record
    /\ IF FIX_RECORD
       THEN upsertIndex' = advIndex   \* FIX: same record
       ELSE UNCHANGED upsertIndex      \* BUG: reads stale record
    /\ UNCHANGED <<uiIndex, advIndex, llmIndex, connected, stopVisible, pc>>

\* Move-on intent detected — stop controls shown, voice stays connected
\* Source: RecallScreen.tsx:531-545 (detectMoveOnIntent handler)
DetectMoveOn ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ stopVisible' = TRUE
    /\ pc' = "stop_presented"
    /\ UNCHANGED <<uiIndex, advIndex, upsertIndex, llmIndex, llmSpeaking, connected, userSpoke>>

\* Manual stop — disconnects, shows stop controls
\* Source: RecallScreen.tsx:403-407 (handleRecord when connected)
ManualStop ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ connected' = FALSE
    /\ llmIndex' = -1
    /\ llmSpeaking' = FALSE
    /\ stopVisible' = TRUE
    /\ pc' = "stop_presented"
    /\ UNCHANGED <<uiIndex, advIndex, upsertIndex, userSpoke>>

\* User taps "Next question" while voice connected (COMPOUND BUG PATH)
\* Source: RecallScreen.tsx:331-360 (advanceQuestionFlow)
\*
\* HAR trace:
\*   Entry 23 (14:50:20): advance_question → currentIndex=1
\*   Entry 24 (14:51:41): update_working_answer → currentIndex=0 (REGRESSION)
\*
\* advanceQuestionFlow does:
\*   1. Local UI advance (line 333-335)
\*   2. Backend advance_question call (line 340)
\*   3. syncActiveQuestionInstructions → session.update (line 359)
\*
\* Bug: upsert path still reads old record with index=0
\* Bug: LLM goes silent after session.update (no auto-speak)
AdvanceWhileConnected ==
    /\ pc = "stop_presented"
    /\ connected = TRUE
    /\ uiIndex < MAX_Q - 1
    \* Step 1: UI advances immediately
    /\ uiIndex' = uiIndex + 1
    /\ stopVisible' = FALSE
    \* Step 2: Backend advance_question updates its record
    /\ \/ advIndex' = uiIndex + 1          \* success
       \/ advIndex' = advIndex              \* failure
    \* Step 3: session.update sent → LLM gets new instructions
    /\ llmIndex' = uiIndex + 1
    \* BUG: LLM goes silent after session.update (no auto-speak)
    \* FIX_REPROMPT: send response.create to trigger LLM speech
    /\ IF FIX_REPROMPT
       THEN llmSpeaking' = TRUE
       ELSE llmSpeaking' = FALSE            \* BUG: silence
    \* Backend upsert path:
    \* FIX_RECORD: both paths resolve same record, so upsert reads advIndex'
    \* BUG: upsert path reads a different record, stays stale
    /\ IF FIX_RECORD
       THEN upsertIndex' = advIndex'        \* FIX: same record
       ELSE upsertIndex' = upsertIndex      \* BUG: different record, stale
    /\ userSpoke' = FALSE                    \* reset for new question
    /\ connected' = TRUE
    /\ pc' = "listening"

\* User speaks after advance while LLM is silent (triggers correction)
\* Source: HAR entry 24 — user says "ok" to break LLM silence
\* The LLM then responds (possibly reading wrong question initially)
UserBreaksSilence ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ llmSpeaking = FALSE
    /\ userSpoke' = TRUE
    /\ llmSpeaking' = TRUE                  \* LLM responds to user
    \* Backend upsert returns regressed index
    /\ IF FIX_RECORD
       THEN upsertIndex' = advIndex
       ELSE UNCHANGED upsertIndex            \* BUG: still stale
    /\ UNCHANGED <<uiIndex, advIndex, llmIndex, connected, stopVisible, pc>>

\* UI refetches from backend (page focus, effect re-run, manual refresh)
\* Source: RecallScreen.tsx:255-296 (useEffect that loads voice turns)
\* getSessionVoiceTurns → reads from resolveStoryRecordBySource
\* If this resolves via the upsert path's record, UI regresses
\* UI refetches from backend (page focus, effect re-run, manual refresh)
\* Source: RecallScreen.tsx:255-296 (useEffect that loads voice turns)
\* The refetch resolves via resolveStoryRecordBySource which may hit
\* either the canonical or upsert record depending on the source path.
\* BUG: can regress uiIndex when upsert path returns stale index
UIRefetch ==
    /\ pc \in {"listening", "stop_presented"}
    /\ ~connected                                 \* refetch only triggers on mount/remount
    /\ IF FIX_RECORD
       THEN /\ uiIndex' = advIndex                \* FIX: always reads canonical record
            /\ advIndex >= uiIndex                 \* guard: backend must be >= local to adopt
       ELSE \/ /\ uiIndex' = advIndex              \* canonical record
            \/ /\ uiIndex' = upsertIndex           \* BUG: stale upsert record
    /\ UNCHANGED <<advIndex, upsertIndex, llmIndex, llmSpeaking, connected, userSpoke, stopVisible, pc>>

\* Advance while disconnected (SAFE PATH)
AdvanceWhileDisconnected ==
    /\ pc = "stop_presented"
    /\ connected = FALSE
    /\ uiIndex < MAX_Q - 1
    /\ uiIndex' = uiIndex + 1
    /\ stopVisible' = FALSE
    /\ \/ advIndex' = uiIndex + 1
       \/ advIndex' = advIndex
    /\ IF FIX_RECORD
       THEN upsertIndex' = advIndex'
       ELSE upsertIndex' = upsertIndex
    /\ pc' = "idle"
    /\ UNCHANGED <<llmIndex, llmSpeaking, connected, userSpoke>>

\* Finish to review on last question
FinishToReview ==
    /\ pc = "stop_presented"
    /\ uiIndex >= MAX_Q - 1
    /\ uiIndex' = MAX_Q
    /\ \/ advIndex' = MAX_Q
       \/ advIndex' = advIndex
    /\ IF FIX_RECORD
       THEN upsertIndex' = advIndex'
       ELSE UNCHANGED upsertIndex
    /\ connected' = FALSE
    /\ llmIndex' = -1
    /\ llmSpeaking' = FALSE
    /\ stopVisible' = FALSE
    /\ pc' = "all_complete"
    /\ UNCHANGED <<userSpoke>>

\* Re-record while disconnected
ReRecordDisconnected ==
    /\ pc = "stop_presented"
    /\ connected = FALSE
    /\ uiIndex < MAX_Q
    /\ connected' = TRUE
    /\ llmIndex' = uiIndex
    /\ llmSpeaking' = TRUE
    /\ stopVisible' = FALSE
    /\ userSpoke' = FALSE
    /\ pc' = "listening"
    /\ UNCHANGED <<uiIndex, advIndex, upsertIndex>>

\* Session timeout or error
SessionTimeout ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ connected' = FALSE
    /\ llmIndex' = -1
    /\ llmSpeaking' = FALSE
    /\ stopVisible' = FALSE
    /\ pc' = "idle"
    /\ UNCHANGED <<uiIndex, advIndex, upsertIndex, userSpoke>>

\* Terminal
Done ==
    /\ pc = "all_complete"
    /\ UNCHANGED vars

Next ==
    \/ VoiceConnect
    \/ UserSpeaks
    \/ DetectMoveOn
    \/ ManualStop
    \/ AdvanceWhileConnected
    \/ UserBreaksSilence
    \/ UIRefetch
    \/ AdvanceWhileDisconnected
    \/ FinishToReview
    \/ ReRecordDisconnected
    \/ SessionTimeout
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ===================================================================== *)
(* INVARIANTS                                                              *)
(* ===================================================================== *)

\* Connected implies LLM has valid question
ErrorConsistency ==
    connected => llmIndex >= 0

\* BUG 1 SIGNATURE: Backend paths must agree on currentIndex
\* Expected: VIOLATED when FIX_RECORD = FALSE
BackendConsistency ==
    advIndex = upsertIndex

\* BUG 2 SIGNATURE: After advance while connected, LLM must auto-speak
\* the new question greeting without waiting for user input.
\* Expected: VIOLATED when FIX_REPROMPT = FALSE
NoLLMSilenceAfterAdvance ==
    ~(pc = "listening" /\ connected /\ ~llmSpeaking /\ uiIndex > 0)

\* BUG 3 SIGNATURE: UI must never regress below advance path
\* Expected: VIOLATED when FIX_RECORD = FALSE (UIRefetch can regress)
UINotBehindAdvance ==
    uiIndex >= advIndex \/ pc = "all_complete"

\* Combined desync: UI and LLM must agree while listening
NoSilentDesync ==
    ~(pc = "listening" /\ connected /\ uiIndex # llmIndex)

\* UI must not be behind upsert path's reported index
\* This can be violated when upsertIndex regresses (it reports 0 while UI is at 1)
\* Actually this is the inverse: upsertIndex can be BEHIND uiIndex which is fine.
\* The danger is UIRefetch adopting the stale upsertIndex.
\* Model this as: advIndex and upsertIndex must agree
BackendRecordSync ==
    (pc # "idle" /\ advIndex > 0) => upsertIndex >= advIndex

(* ===================================================================== *)
(* TEMPORAL PROPERTIES                                                     *)
(* ===================================================================== *)

\* After advance, LLM must eventually speak or disconnect
LLMEventualResponse ==
    [](pc = "listening" /\ connected /\ ~llmSpeaking
        => <>(llmSpeaking \/ ~connected))

\* UI index never decreases (monotonic progression)
MonotonicProgress == [][uiIndex' >= uiIndex]_uiIndex

\* After advance, backend paths eventually agree or system terminates
BackendEventualSync ==
    [](advIndex # upsertIndex
        => <>(advIndex = upsertIndex \/ pc = "all_complete"))

====
