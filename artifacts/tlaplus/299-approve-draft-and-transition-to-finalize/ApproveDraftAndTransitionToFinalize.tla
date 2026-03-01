---- MODULE ApproveDraftAndTransitionToFinalize ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_w8p2, ui_v3n6, ui_a4y1, api_q7v1, api_m5g7, api_n8k2, db_h2s4, db_d3w8, db_f8n5, db_l1c3, cfg_j9w2, cfg_q9c5, cfg_p4b8, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "step_5", "step_6", "done", "error"}

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

\* --- Step actions ---
Step1_Capture_Approve_Action ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Invoke_Approval_Endpoint ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Process_Approval_Request ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out >>

Step4_Persist_Session_State_Transition ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out >>

Step5_Log_Approval_Event ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out >>

Step6_Return_Updated_Session_to_UI ==
    /\ pc = "step_5"
    /\ pc' = "done"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

\* --- Error actions ---
Step1_Capture_Approve_Action_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Invoke_Approval_Endpoint_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Process_Approval_Request_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step4_Persist_Session_State_Transition_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step5_Log_Approval_Event_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step6_Return_Updated_Session_to_UI_Error ==
    /\ pc = "step_5"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Next ==
    \/ Step1_Capture_Approve_Action
    \/ Step2_Invoke_Approval_Endpoint
    \/ Step3_Process_Approval_Request
    \/ Step4_Persist_Session_State_Transition
    \/ Step5_Log_Approval_Event
    \/ Step6_Return_Updated_Session_to_UI
    \/ Step1_Capture_Approve_Action_Error
    \/ Step2_Invoke_Approval_Endpoint_Error
    \/ Step3_Process_Approval_Request_Error
    \/ Step4_Persist_Session_State_Transition_Error
    \/ Step5_Log_Approval_Event_Error
    \/ Step6_Return_Updated_Session_to_UI_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
