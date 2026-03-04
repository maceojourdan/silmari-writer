---- MODULE FileUploadRecallQuestionsModel ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_v3n6, ui_w8p2, db_h2s4, cfg_k3x7, api_u1r9, api_f2k8, db_r5m3, fn_q4w2, fn_d7j1

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "step_5", "step_6", "step_7", "done", "error"}

ErrorConsistency ==
    error_state = TRUE => pc = "error"

Init ==
    /\ pc = "idle"
    /\ error_state = FALSE
    /\ step_1_out = "none"
    /\ step_2_out = "none"
    /\ step_3_out = "none"
    /\ step_4_out = "none"
    /\ step_5_out = "none"
    /\ step_6_out = "none"
    /\ step_7_out = "none"

\* --- Step actions ---
Step1_SelectInputMode ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step2_ProcessInput ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step3_ResolveQuestions ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step4_InitializeQuestionState ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out, step_7_out >>

Step5_DisplayRecallQuestion ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out, step_7_out >>

Step6_CaptureQuestionResponse ==
    /\ pc = "step_5"
    /\ pc' = "step_6"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_7_out >>

Step7_AdvanceToNextQuestion ==
    /\ pc = "step_6"
    /\ pc' = "done"
    /\ step_7_out' = "step_7_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

\* --- Error actions ---
Step1_SelectInputMode_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step3_ResolveQuestions_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step4_InitializeQuestionState_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step5_DisplayRecallQuestion_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step6_CaptureQuestionResponse_Error ==
    /\ pc = "step_5"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step7_AdvanceToNextQuestion_Error ==
    /\ pc = "step_6"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Next ==
    \/ Step1_SelectInputMode
    \/ Step2_ProcessInput
    \/ Step3_ResolveQuestions
    \/ Step4_InitializeQuestionState
    \/ Step5_DisplayRecallQuestion
    \/ Step6_CaptureQuestionResponse
    \/ Step7_AdvanceToNextQuestion
    \/ Step1_SelectInputMode_Error
    \/ Step3_ResolveQuestions_Error
    \/ Step4_InitializeQuestionState_Error
    \/ Step5_DisplayRecallQuestion_Error
    \/ Step6_CaptureQuestionResponse_Error
    \/ Step7_AdvanceToNextQuestion_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
