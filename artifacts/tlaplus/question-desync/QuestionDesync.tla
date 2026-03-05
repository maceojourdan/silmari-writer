---- MODULE QuestionDesync ----
(***************************************************************************)
(* Models the three-actor question state desync bug in RecallScreen.       *)
(*                                                                         *)
(* Three actors hold question state:                                       *)
(*   1. UI (React state) — uiIndex                                        *)
(*   2. Backend (DB story record) — dbIndex                                *)
(*   3. LLM (realtime session instructions) — llmIndex                    *)
(*                                                                         *)
(* Bug: advanceQuestionFlow() advances UI and backend but never            *)
(* reconnects/updates the LLM session instructions. When the voice         *)
(* session remains connected through a question advance (move-on intent    *)
(* path), the LLM keeps coaching the old question while UI shows the new.  *)
(*                                                                         *)
(* FIX_ENABLED = TRUE adds a SyncLLM effect to AdvanceWhileConnected      *)
(* that updates llmIndex to match uiIndex after advancement.               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    MAX_Q,          \* Number of questions (e.g. 4). Indices 0..MAX_Q-1 are questions, MAX_Q = done
    FIX_ENABLED     \* TRUE = sync LLM on advance; FALSE = current buggy behavior

VARIABLES
    uiIndex,        \* 0..MAX_Q: question index the UI displays
    dbIndex,        \* 0..MAX_Q: question index persisted in backend story record
    llmIndex,       \* -1..MAX_Q: question index baked into LLM instructions (-1 = no session)
    connected,      \* BOOLEAN: whether realtime voice session is active
    stopVisible,    \* BOOLEAN: whether stop controls are shown in UI
    pc              \* program counter / component state

vars == <<uiIndex, dbIndex, llmIndex, connected, stopVisible, pc>>

TypeInvariant ==
    /\ uiIndex \in 0..MAX_Q
    /\ dbIndex \in 0..MAX_Q
    /\ llmIndex \in -1..MAX_Q
    /\ connected \in BOOLEAN
    /\ stopVisible \in BOOLEAN
    /\ pc \in {"idle", "listening", "stop_presented", "all_complete"}

Init ==
    /\ uiIndex = 0
    /\ dbIndex = 0
    /\ llmIndex = -1
    /\ connected = FALSE
    /\ stopVisible = FALSE
    /\ pc = "idle"

(* ===================================================================== *)
(* TRANSITIONS                                                            *)
(* ===================================================================== *)

\* User clicks Record → voice session connects with current question
\* Source: RecallScreen.tsx:380-407 (handleRecord)
VoiceConnect ==
    /\ pc = "idle"
    /\ uiIndex < MAX_Q
    /\ connected' = TRUE
    /\ llmIndex' = uiIndex    \* instructions set once at connect() time
    /\ pc' = "listening"
    /\ UNCHANGED <<uiIndex, dbIndex, stopVisible>>

\* Move-on intent detected in voice transcript — stop controls shown,
\* voice session STAYS CONNECTED (this is the dangerous path)
\* Source: RecallScreen.tsx:516-529 (detectMoveOnIntent handler)
DetectMoveOn ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ stopVisible' = TRUE
    /\ pc' = "stop_presented"
    /\ UNCHANGED <<uiIndex, dbIndex, llmIndex, connected>>

\* User manually clicks Stop button — disconnects, then shows stop controls
\* Source: RecallScreen.tsx:388-392 (handleRecord when isConnected)
ManualStop ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ connected' = FALSE
    /\ llmIndex' = -1
    /\ stopVisible' = TRUE
    /\ pc' = "stop_presented"
    /\ UNCHANGED <<uiIndex, dbIndex>>

\* User clicks "Next question" while voice still connected (THE BUG PATH)
\* Source: RecallScreen.tsx:317-345 (advanceQuestionFlow)
\* UI advances immediately (line 321), backend call is async (line 326),
\* LLM instructions are NEVER updated — no disconnect/reconnect occurs.
AdvanceWhileConnected ==
    /\ pc = "stop_presented"
    /\ connected = TRUE
    /\ uiIndex < MAX_Q - 1    \* not the last question
    /\ uiIndex' = uiIndex + 1
    /\ stopVisible' = FALSE
    \* Backend: nondeterministic success/fail
    /\ \/ dbIndex' = uiIndex + 1     \* backend advance succeeds
       \/ dbIndex' = dbIndex          \* backend fails (network, resolver, etc.)
    \* LLM sync: THIS IS WHERE THE BUG LIVES
    /\ IF FIX_ENABLED
       THEN llmIndex' = uiIndex + 1  \* FIX: resync LLM via reconnect or session.update
       ELSE llmIndex' = llmIndex      \* BUG: LLM keeps old question instructions
    /\ connected' = TRUE
    /\ pc' = "listening"

\* User clicks "Next question" while disconnected (SAFE PATH)
\* LLM is already off; next Record will connect with correct question.
AdvanceWhileDisconnected ==
    /\ pc = "stop_presented"
    /\ connected = FALSE
    /\ uiIndex < MAX_Q - 1
    /\ uiIndex' = uiIndex + 1
    /\ stopVisible' = FALSE
    /\ \/ dbIndex' = uiIndex + 1
       \/ dbIndex' = dbIndex
    /\ pc' = "idle"
    /\ UNCHANGED <<llmIndex, connected>>

\* User clicks "Finish to Review" on the last question
\* Source: RecallScreen.tsx:751-753 (button label logic + advanceQuestionFlow terminal)
FinishToReview ==
    /\ pc = "stop_presented"
    /\ uiIndex >= MAX_Q - 1
    /\ uiIndex' = MAX_Q
    /\ \/ dbIndex' = MAX_Q
       \/ dbIndex' = dbIndex
    /\ connected' = FALSE
    /\ llmIndex' = -1
    /\ stopVisible' = FALSE
    /\ pc' = "all_complete"

\* Re-record while disconnected: reconnect with CURRENT question
\* Source: RecallScreen.tsx:724-729 → handleRecord when !isConnected
\* This path is safe: connect() uses current activeQuestion
ReRecordDisconnected ==
    /\ pc = "stop_presented"
    /\ connected = FALSE
    /\ uiIndex < MAX_Q
    /\ connected' = TRUE
    /\ llmIndex' = uiIndex     \* fresh connect → correct instructions
    /\ stopVisible' = FALSE
    /\ pc' = "listening"
    /\ UNCHANGED <<uiIndex, dbIndex>>

\* Re-record while connected: code disconnects first, stays in stop_presented
\* Source: RecallScreen.tsx:724-729 → handleRecord when isConnected
\* handleRecord sees isConnected → disconnect() → presentStopState('manual_stop')
ReRecordConnected ==
    /\ pc = "stop_presented"
    /\ connected = TRUE
    /\ connected' = FALSE
    /\ llmIndex' = -1
    \* pc stays stop_presented; user must click Re-record again to reconnect
    /\ UNCHANGED <<uiIndex, dbIndex, stopVisible, pc>>

\* Voice session disconnects unexpectedly (timeout, network, error)
SessionTimeout ==
    /\ pc = "listening"
    /\ connected = TRUE
    /\ connected' = FALSE
    /\ llmIndex' = -1
    /\ stopVisible' = FALSE
    /\ pc' = "idle"
    /\ UNCHANGED <<uiIndex, dbIndex>>

\* Terminal stuttering
Done ==
    /\ pc = "all_complete"
    /\ UNCHANGED vars

Next ==
    \/ VoiceConnect
    \/ DetectMoveOn
    \/ ManualStop
    \/ AdvanceWhileConnected
    \/ AdvanceWhileDisconnected
    \/ FinishToReview
    \/ ReRecordDisconnected
    \/ ReRecordConnected
    \/ SessionTimeout
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ===================================================================== *)
(* INVARIANTS (state predicates)                                          *)
(* ===================================================================== *)

\* Connected implies LLM has a valid question configured
ErrorConsistency ==
    connected => llmIndex >= 0

\* BUG SIGNATURE: UI and LLM must not disagree while actively listening
\* Expected: VIOLATED when FIX_ENABLED = FALSE
NoSilentDesync ==
    ~(pc = "listening" /\ connected /\ uiIndex # llmIndex)

\* When all three actors are in stable listening state with DB synced,
\* LLM must also be synced
FullTripleSync ==
    (pc = "listening" /\ connected /\ dbIndex = uiIndex) => llmIndex = uiIndex

\* UI must never fall behind LLM (UI is the source of truth for progression)
UINotBehindLLM ==
    connected => uiIndex >= llmIndex

(* ===================================================================== *)
(* TEMPORAL PROPERTIES (require PROPERTIES in cfg, not INVARIANTS)        *)
(* ===================================================================== *)

\* If user has completed all questions, system must be in terminal state
Reachability == uiIndex >= MAX_Q => pc = "all_complete"

\* UI question index never decreases
MonotonicProgress == [][uiIndex' >= uiIndex]_uiIndex

\* After desync occurs while connected, LLM eventually resyncs or disconnects
\* Expected: VIOLATED when FIX_ENABLED = FALSE (infinite desync loop possible)
LLMEventualResync ==
    [](pc = "listening" /\ connected /\ uiIndex # llmIndex
        => <>(llmIndex = uiIndex \/ ~connected))

====
