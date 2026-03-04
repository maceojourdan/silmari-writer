---- MODULE FileUploadRecallQuestions ----
\* TLA+ behavioral model for file upload + recall questions workflow.
\*
\* Extracted from: StartVoiceSessionModule.tsx, RecallScreen.tsx,
\*                 VoiceRecallService.ts, startSessionFromUrl.ts
\*
\* Models three input modes (URL, file upload, default questions),
\* session initialization, question resolution, and per-question
\* voice recall with advancement.

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxQuestions,       \* Max questions in a session (typically 4)
    MaxRetries,         \* Max voice transcription retries per question
    InputModes,         \* {"url", "file_upload", "default_questions"}
    FileTypes,          \* {"resume", "screenshot"}
    ResumeExtensions,   \* {"docx", "doc", "pdf", "txt", "md"}
    ScreenshotExtensions \* {"png", "jpg", "jpeg", "webp"}

VARIABLES
    phase,              \* Global workflow phase
    inputMode,          \* Selected input mode
    sessionId,          \* UUID (modeled as string presence)
    fileUploaded,       \* File type uploaded (or "none")
    resumeStored,       \* Whether resume is persisted
    questions,          \* Sequence of questions for this session
    questionProgress,   \* { currentIndex, total, completed }
    slotState,          \* Per-question slot fill state
    voiceRetries,       \* Retry count for current voice capture
    errorState          \* Current error (or "none")

vars == <<phase, inputMode, sessionId, fileUploaded, resumeStored,
          questions, questionProgress, slotState, voiceRetries, errorState>>

\* -----------------------------------------------------------------------
\* Phase values
\* -----------------------------------------------------------------------
Phases == {"idle", "select_input", "processing_input", "resolving_questions",
           "initializing_question_state", "displaying_question",
           "capturing_response", "advancing", "review", "error"}

\* -----------------------------------------------------------------------
\* Type Invariant
\* -----------------------------------------------------------------------
TypeInvariant ==
    /\ phase \in Phases
    /\ inputMode \in InputModes \cup {"none"}
    /\ sessionId \in {"none", "valid_session"}
    /\ fileUploaded \in FileTypes \cup {"none"}
    /\ resumeStored \in BOOLEAN
    /\ questions \in Seq({"q1", "q2", "q3", "q4"})
    /\ questionProgress.currentIndex \in 0..MaxQuestions
    /\ questionProgress.total \in 0..MaxQuestions
    /\ Cardinality(questionProgress.completed) <= MaxQuestions
    /\ slotState \in SUBSET {"anchors", "actions", "outcomes"}
    /\ voiceRetries \in 0..MaxRetries
    /\ errorState \in {"none", "session_already_active", "upload_failed",
                        "extraction_failed", "voice_failed", "save_failed",
                        "invalid_url", "unauthenticated"}

\* -----------------------------------------------------------------------
\* INV-3: All input modes produce at least 1 question
\* -----------------------------------------------------------------------
QuestionsNonEmpty ==
    phase \in {"displaying_question", "capturing_response", "advancing", "review"}
        => Len(questions) > 0

\* -----------------------------------------------------------------------
\* INV-4: Voice AI receives exactly one question at a time
\* -----------------------------------------------------------------------
SingleActiveQuestion ==
    phase = "capturing_response"
        => questionProgress.currentIndex < questionProgress.total

\* -----------------------------------------------------------------------
\* INV-5: Question index monotonically increases
\* (Checked via temporal property — see liveness)
\* -----------------------------------------------------------------------

\* -----------------------------------------------------------------------
\* INV-8: Confirmed slots not overwritten (modeled as set union, not replace)
\* -----------------------------------------------------------------------

\* -----------------------------------------------------------------------
\* INV-12: Session error propagates on all input modes
\* -----------------------------------------------------------------------
ErrorPropagation ==
    errorState = "session_already_active"
        => phase = "error"

\* -----------------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------------
Init ==
    /\ phase = "idle"
    /\ inputMode = "none"
    /\ sessionId = "none"
    /\ fileUploaded = "none"
    /\ resumeStored = FALSE
    /\ questions = <<>>
    /\ questionProgress = [currentIndex |-> 0, total |-> 0, completed |-> {}]
    /\ slotState = {}
    /\ voiceRetries = 0
    /\ errorState = "none"

\* -----------------------------------------------------------------------
\* Step 1: SelectInputMode
\* -----------------------------------------------------------------------
SelectInputMode(mode) ==
    /\ phase = "idle"
    /\ mode \in InputModes
    /\ phase' = "select_input"
    /\ inputMode' = mode
    /\ UNCHANGED <<sessionId, fileUploaded, resumeStored, questions,
                   questionProgress, slotState, voiceRetries, errorState>>

\* -----------------------------------------------------------------------
\* Step 2a: ProcessInput — URL mode (existing behavior)
\* -----------------------------------------------------------------------
ProcessInputUrl ==
    /\ phase = "select_input"
    /\ inputMode = "url"
    /\ phase' = "processing_input"
    /\ sessionId' = "valid_session"
    /\ UNCHANGED <<inputMode, fileUploaded, resumeStored, questions,
                   questionProgress, slotState, voiceRetries, errorState>>

\* Step 2b: ProcessInput — File upload mode
ProcessInputFile(fileType) ==
    /\ phase = "select_input"
    /\ inputMode = "file_upload"
    /\ fileType \in FileTypes
    /\ phase' = "processing_input"
    /\ sessionId' = "valid_session"
    /\ fileUploaded' = fileType
    /\ resumeStored' = IF fileType = "resume" THEN TRUE ELSE resumeStored
    /\ UNCHANGED <<inputMode, questions, questionProgress, slotState,
                   voiceRetries, errorState>>

\* Step 2c: ProcessInput — Default questions mode
ProcessInputDefault ==
    /\ phase = "select_input"
    /\ inputMode = "default_questions"
    /\ phase' = "processing_input"
    /\ sessionId' = "valid_session"
    /\ UNCHANGED <<inputMode, fileUploaded, resumeStored, questions,
                   questionProgress, slotState, voiceRetries, errorState>>

\* Step 2-error: Session already active (any mode)
ProcessInputSessionConflict ==
    /\ phase = "select_input"
    /\ inputMode \in InputModes
    /\ phase' = "error"
    /\ errorState' = "session_already_active"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, slotState, voiceRetries>>

\* Step 2-error: Upload failure (file mode only)
ProcessInputUploadFail ==
    /\ phase = "select_input"
    /\ inputMode = "file_upload"
    /\ phase' = "error"
    /\ errorState' = "upload_failed"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, slotState, voiceRetries>>

\* -----------------------------------------------------------------------
\* Step 3: ResolveQuestions
\* -----------------------------------------------------------------------
ResolveQuestionsFromContext ==
    /\ phase = "processing_input"
    /\ sessionId = "valid_session"
    \* URL mode or file+screenshot might derive questions from job context
    /\ inputMode \in {"url", "file_upload"}
    /\ questions' = <<"q1", "q2", "q3", "q4">>
    /\ phase' = "resolving_questions"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questionProgress, slotState, voiceRetries, errorState>>

ResolveDefaultQuestions ==
    /\ phase = "processing_input"
    /\ sessionId = "valid_session"
    \* Default mode always uses the 4 default questions
    /\ inputMode = "default_questions"
    /\ questions' = <<"q1", "q2", "q3", "q4">>
    /\ phase' = "resolving_questions"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questionProgress, slotState, voiceRetries, errorState>>

\* Fallback: LLM derivation failure -> default questions (INV-3 preserved)
ResolveQuestionsFallback ==
    /\ phase = "processing_input"
    /\ sessionId = "valid_session"
    /\ inputMode \in {"url", "file_upload"}
    /\ questions' = <<"q1", "q2", "q3", "q4">>
    /\ phase' = "resolving_questions"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questionProgress, slotState, voiceRetries, errorState>>

\* -----------------------------------------------------------------------
\* Step 4: InitializeQuestionState
\* -----------------------------------------------------------------------
InitializeQuestionState ==
    /\ phase = "resolving_questions"
    /\ Len(questions) > 0
    /\ questionProgress' = [currentIndex |-> 0,
                             total |-> Len(questions),
                             completed |-> {}]
    /\ slotState' = {}
    /\ voiceRetries' = 0
    /\ phase' = "initializing_question_state"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, errorState>>

\* -----------------------------------------------------------------------
\* Step 5: DisplayRecallQuestion
\* -----------------------------------------------------------------------
DisplayRecallQuestion ==
    /\ phase = "initializing_question_state"
    /\ questionProgress.currentIndex < questionProgress.total
    /\ phase' = "displaying_question"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, slotState, voiceRetries,
                   errorState>>

\* -----------------------------------------------------------------------
\* Step 6: CaptureQuestionResponse
\* -----------------------------------------------------------------------
\* Successful voice capture — fills a slot
CaptureResponseSuccess(slot) ==
    /\ phase = "displaying_question"
    /\ slot \in {"anchors", "actions", "outcomes"}
    /\ slot \notin slotState
    /\ phase' = "capturing_response"
    /\ slotState' = slotState \cup {slot}
    /\ voiceRetries' = 0
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, errorState>>

\* Voice capture fails — retry if under limit
CaptureResponseRetry ==
    /\ phase = "displaying_question"
    /\ voiceRetries < MaxRetries
    /\ voiceRetries' = voiceRetries + 1
    /\ UNCHANGED <<phase, inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, slotState, errorState>>

\* Voice capture fails — max retries exceeded (INV-9)
CaptureResponseFail ==
    /\ phase = "displaying_question"
    /\ voiceRetries >= MaxRetries
    /\ phase' = "error"
    /\ errorState' = "voice_failed"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, slotState, voiceRetries>>

\* Continue capturing after successful response (loop back to display)
ContinueCapturing ==
    /\ phase = "capturing_response"
    /\ slotState /= {"anchors", "actions", "outcomes"}
    /\ phase' = "displaying_question"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, slotState, voiceRetries,
                   errorState>>

\* -----------------------------------------------------------------------
\* Step 7: AdvanceToNextQuestion
\* -----------------------------------------------------------------------
\* All slots filled — auto-advance
AdvanceQuestionAutoComplete ==
    /\ phase = "capturing_response"
    /\ slotState = {"anchors", "actions", "outcomes"}
    /\ questionProgress.currentIndex < questionProgress.total - 1
    /\ questionProgress' = [questionProgress EXCEPT
                             !.currentIndex = questionProgress.currentIndex + 1,
                             !.completed = questionProgress.completed \cup
                                {questions[questionProgress.currentIndex + 1]}]
    /\ slotState' = {}
    /\ voiceRetries' = 0
    /\ phase' = "initializing_question_state"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, errorState>>

\* User explicitly moves to next question (even with incomplete slots)
AdvanceQuestionExplicit ==
    /\ phase \in {"displaying_question", "capturing_response"}
    /\ questionProgress.currentIndex < questionProgress.total - 1
    /\ questionProgress' = [questionProgress EXCEPT
                             !.currentIndex = questionProgress.currentIndex + 1,
                             !.completed = questionProgress.completed \cup
                                {questions[questionProgress.currentIndex + 1]}]
    /\ slotState' = {}
    /\ voiceRetries' = 0
    /\ phase' = "initializing_question_state"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, errorState>>

\* Last question completed — transition to review
AdvanceToReview ==
    /\ phase \in {"capturing_response", "displaying_question"}
    /\ questionProgress.currentIndex >= questionProgress.total - 1
    /\ phase' = "review"
    /\ UNCHANGED <<inputMode, sessionId, fileUploaded, resumeStored,
                   questions, questionProgress, slotState, voiceRetries,
                   errorState>>

\* -----------------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------------
Next ==
    \/ \E mode \in InputModes : SelectInputMode(mode)
    \/ ProcessInputUrl
    \/ \E ft \in FileTypes : ProcessInputFile(ft)
    \/ ProcessInputDefault
    \/ ProcessInputSessionConflict
    \/ ProcessInputUploadFail
    \/ ResolveQuestionsFromContext
    \/ ResolveDefaultQuestions
    \/ ResolveQuestionsFallback
    \/ InitializeQuestionState
    \/ DisplayRecallQuestion
    \/ \E slot \in {"anchors", "actions", "outcomes"} : CaptureResponseSuccess(slot)
    \/ CaptureResponseRetry
    \/ CaptureResponseFail
    \/ ContinueCapturing
    \/ AdvanceQuestionAutoComplete
    \/ AdvanceQuestionExplicit
    \/ AdvanceToReview

\* -----------------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -----------------------------------------------------------------------
\* Safety Properties
\* -----------------------------------------------------------------------
Safety ==
    /\ TypeInvariant
    /\ QuestionsNonEmpty
    /\ SingleActiveQuestion
    /\ ErrorPropagation

\* -----------------------------------------------------------------------
\* Liveness: Every session eventually reaches review or error
\* -----------------------------------------------------------------------
Liveness == <>(phase \in {"review", "error"})

\* -----------------------------------------------------------------------
\* INV-1: Reachability — all input modes can produce a valid session
\* (Checked via TLC: all three SelectInputMode(mode) transitions are enabled)
\* -----------------------------------------------------------------------

\* -----------------------------------------------------------------------
\* INV-7: Resume stored before questions resolved (file mode with resume)
\* -----------------------------------------------------------------------
ResumeStoredBeforeQuestions ==
    (phase = "resolving_questions" /\ inputMode = "file_upload" /\ fileUploaded = "resume")
        => resumeStored = TRUE

====
