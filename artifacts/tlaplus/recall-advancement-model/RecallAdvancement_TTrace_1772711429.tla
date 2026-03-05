---- MODULE RecallAdvancement_TTrace_1772711429 ----
EXTENDS RecallAdvancement, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET RecallAdvancement_TEExpression == INSTANCE RecallAdvancement_TEExpression
    IN RecallAdvancement_TEExpression!expression
----

_trace ==
    LET RecallAdvancement_TETrace == INSTANCE RecallAdvancement_TETrace
    IN RecallAdvancement_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        sessionSource = ("session")
        /\
        pc = ("all_complete")
        /\
        slotsComplete = (TRUE)
        /\
        storyRecordFound = (TRUE)
        /\
        recordLinkMode = ("session_id")
        /\
        advanceInFlight = (FALSE)
        /\
        currentIndex = (4)
    )
----

_init ==
    /\ recordLinkMode = _TETrace[1].recordLinkMode
    /\ storyRecordFound = _TETrace[1].storyRecordFound
    /\ pc = _TETrace[1].pc
    /\ sessionSource = _TETrace[1].sessionSource
    /\ currentIndex = _TETrace[1].currentIndex
    /\ slotsComplete = _TETrace[1].slotsComplete
    /\ advanceInFlight = _TETrace[1].advanceInFlight
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ recordLinkMode  = _TETrace[i].recordLinkMode
        /\ recordLinkMode' = _TETrace[j].recordLinkMode
        /\ storyRecordFound  = _TETrace[i].storyRecordFound
        /\ storyRecordFound' = _TETrace[j].storyRecordFound
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc
        /\ sessionSource  = _TETrace[i].sessionSource
        /\ sessionSource' = _TETrace[j].sessionSource
        /\ currentIndex  = _TETrace[i].currentIndex
        /\ currentIndex' = _TETrace[j].currentIndex
        /\ slotsComplete  = _TETrace[i].slotsComplete
        /\ slotsComplete' = _TETrace[j].slotsComplete
        /\ advanceInFlight  = _TETrace[i].advanceInFlight
        /\ advanceInFlight' = _TETrace[j].advanceInFlight

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("RecallAdvancement_TTrace_1772711429.json", _TETrace)

=============================================================================

 Note that you can extract this module `RecallAdvancement_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `RecallAdvancement_TEExpression.tla` file takes precedence 
  over the module `RecallAdvancement_TEExpression` below).

---- MODULE RecallAdvancement_TEExpression ----
EXTENDS RecallAdvancement, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `RecallAdvancement` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        recordLinkMode |-> recordLinkMode
        ,storyRecordFound |-> storyRecordFound
        ,pc |-> pc
        ,sessionSource |-> sessionSource
        ,currentIndex |-> currentIndex
        ,slotsComplete |-> slotsComplete
        ,advanceInFlight |-> advanceInFlight
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_recordLinkModeUnchanged |-> recordLinkMode = recordLinkMode'
        
        \* Format the `recordLinkMode` variable as Json value.
        \* ,_recordLinkModeJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(recordLinkMode)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_recordLinkModeModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].recordLinkMode # _TETrace[s-1].recordLinkMode
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE RecallAdvancement_TETrace ----
\*EXTENDS RecallAdvancement, IOUtils, TLC
\*
\*trace == IODeserialize("RecallAdvancement_TTrace_1772711429.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE RecallAdvancement_TETrace ----
EXTENDS RecallAdvancement, TLC

trace == 
    <<
    ([sessionSource |-> "session",pc |-> "idle",slotsComplete |-> TRUE,storyRecordFound |-> FALSE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 0]),
    ([sessionSource |-> "session",pc |-> "move_on_detected",slotsComplete |-> TRUE,storyRecordFound |-> FALSE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 0]),
    ([sessionSource |-> "session",pc |-> "checking_progress",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 0]),
    ([sessionSource |-> "session",pc |-> "advancing",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> TRUE,currentIndex |-> 0]),
    ([sessionSource |-> "session",pc |-> "advanced",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 1]),
    ([sessionSource |-> "session",pc |-> "idle",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 1]),
    ([sessionSource |-> "session",pc |-> "move_on_detected",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 1]),
    ([sessionSource |-> "session",pc |-> "checking_progress",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 1]),
    ([sessionSource |-> "session",pc |-> "advancing",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> TRUE,currentIndex |-> 1]),
    ([sessionSource |-> "session",pc |-> "advanced",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 2]),
    ([sessionSource |-> "session",pc |-> "idle",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 2]),
    ([sessionSource |-> "session",pc |-> "move_on_detected",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 2]),
    ([sessionSource |-> "session",pc |-> "checking_progress",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 2]),
    ([sessionSource |-> "session",pc |-> "advancing",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> TRUE,currentIndex |-> 2]),
    ([sessionSource |-> "session",pc |-> "advanced",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 3]),
    ([sessionSource |-> "session",pc |-> "idle",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 3]),
    ([sessionSource |-> "session",pc |-> "move_on_detected",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 3]),
    ([sessionSource |-> "session",pc |-> "checking_progress",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 3]),
    ([sessionSource |-> "session",pc |-> "advancing",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> TRUE,currentIndex |-> 3]),
    ([sessionSource |-> "session",pc |-> "all_complete",slotsComplete |-> TRUE,storyRecordFound |-> TRUE,recordLinkMode |-> "session_id",advanceInFlight |-> FALSE,currentIndex |-> 4])
    >>
----


=============================================================================

---- CONFIG RecallAdvancement_TTrace_1772711429 ----
CONSTANTS
    NUM_QUESTIONS = 4

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Thu Mar 05 06:50:29 EST 2026