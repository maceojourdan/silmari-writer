---- MODULE VoiceAdvanceRegression_TTrace_1772722862 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, VoiceAdvanceRegression

_expression ==
    LET VoiceAdvanceRegression_TEExpression == INSTANCE VoiceAdvanceRegression_TEExpression
    IN VoiceAdvanceRegression_TEExpression!expression
----

_trace ==
    LET VoiceAdvanceRegression_TETrace == INSTANCE VoiceAdvanceRegression_TETrace
    IN VoiceAdvanceRegression_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        connected = (TRUE)
        /\
        uiIndex = (1)
        /\
        userSpoke = (FALSE)
        /\
        pc = ("listening")
        /\
        llmSpeaking = (TRUE)
        /\
        advIndex = (1)
        /\
        llmIndex = (1)
        /\
        stopVisible = (FALSE)
        /\
        upsertIndex = (0)
    )
----

_init ==
    /\ advIndex = _TETrace[1].advIndex
    /\ connected = _TETrace[1].connected
    /\ uiIndex = _TETrace[1].uiIndex
    /\ pc = _TETrace[1].pc
    /\ upsertIndex = _TETrace[1].upsertIndex
    /\ userSpoke = _TETrace[1].userSpoke
    /\ llmIndex = _TETrace[1].llmIndex
    /\ llmSpeaking = _TETrace[1].llmSpeaking
    /\ stopVisible = _TETrace[1].stopVisible
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ advIndex  = _TETrace[i].advIndex
        /\ advIndex' = _TETrace[j].advIndex
        /\ connected  = _TETrace[i].connected
        /\ connected' = _TETrace[j].connected
        /\ uiIndex  = _TETrace[i].uiIndex
        /\ uiIndex' = _TETrace[j].uiIndex
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc
        /\ upsertIndex  = _TETrace[i].upsertIndex
        /\ upsertIndex' = _TETrace[j].upsertIndex
        /\ userSpoke  = _TETrace[i].userSpoke
        /\ userSpoke' = _TETrace[j].userSpoke
        /\ llmIndex  = _TETrace[i].llmIndex
        /\ llmIndex' = _TETrace[j].llmIndex
        /\ llmSpeaking  = _TETrace[i].llmSpeaking
        /\ llmSpeaking' = _TETrace[j].llmSpeaking
        /\ stopVisible  = _TETrace[i].stopVisible
        /\ stopVisible' = _TETrace[j].stopVisible

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("VoiceAdvanceRegression_TTrace_1772722862.json", _TETrace)

=============================================================================

 Note that you can extract this module `VoiceAdvanceRegression_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `VoiceAdvanceRegression_TEExpression.tla` file takes precedence 
  over the module `VoiceAdvanceRegression_TEExpression` below).

---- MODULE VoiceAdvanceRegression_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, VoiceAdvanceRegression

expression == 
    [
        \* To hide variables of the `VoiceAdvanceRegression` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        advIndex |-> advIndex
        ,connected |-> connected
        ,uiIndex |-> uiIndex
        ,pc |-> pc
        ,upsertIndex |-> upsertIndex
        ,userSpoke |-> userSpoke
        ,llmIndex |-> llmIndex
        ,llmSpeaking |-> llmSpeaking
        ,stopVisible |-> stopVisible
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_advIndexUnchanged |-> advIndex = advIndex'
        
        \* Format the `advIndex` variable as Json value.
        \* ,_advIndexJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(advIndex)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_advIndexModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].advIndex # _TETrace[s-1].advIndex
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE VoiceAdvanceRegression_TETrace ----
\*EXTENDS IOUtils, TLC, VoiceAdvanceRegression
\*
\*trace == IODeserialize("VoiceAdvanceRegression_TTrace_1772722862.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE VoiceAdvanceRegression_TETrace ----
EXTENDS TLC, VoiceAdvanceRegression

trace == 
    <<
    ([connected |-> FALSE,uiIndex |-> 0,userSpoke |-> FALSE,pc |-> "idle",llmSpeaking |-> FALSE,advIndex |-> 0,llmIndex |-> -1,stopVisible |-> FALSE,upsertIndex |-> 0]),
    ([connected |-> TRUE,uiIndex |-> 0,userSpoke |-> FALSE,pc |-> "listening",llmSpeaking |-> TRUE,advIndex |-> 0,llmIndex |-> 0,stopVisible |-> FALSE,upsertIndex |-> 0]),
    ([connected |-> TRUE,uiIndex |-> 0,userSpoke |-> FALSE,pc |-> "stop_presented",llmSpeaking |-> TRUE,advIndex |-> 0,llmIndex |-> 0,stopVisible |-> TRUE,upsertIndex |-> 0]),
    ([connected |-> TRUE,uiIndex |-> 1,userSpoke |-> FALSE,pc |-> "listening",llmSpeaking |-> TRUE,advIndex |-> 1,llmIndex |-> 1,stopVisible |-> FALSE,upsertIndex |-> 0])
    >>
----


=============================================================================

---- CONFIG VoiceAdvanceRegression_TTrace_1772722862 ----
CONSTANTS
    MAX_Q = 4
    FIX_RECORD = TRUE
    FIX_REPROMPT = TRUE

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
\* Generated on Thu Mar 05 10:01:02 EST 2026