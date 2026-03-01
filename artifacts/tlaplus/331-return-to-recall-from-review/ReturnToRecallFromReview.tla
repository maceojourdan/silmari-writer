---- MODULE ReturnToRecallFromReview ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_w8p2, ui_v3n6, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "done", "error"}

ErrorConsistency ==
    error_state = TRUE => pc = "error"

Init ==
    /\ pc = "idle"
    /\ error_state = FALSE
    /\ step_1_out = "none"
    /\ step_2_out = "none"
    /\ step_3_out = "none"

\* --- Step actions ---
Step1_Capture_return_action ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out >>

Step2_Update_writing_flow_state ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out >>

Step3_Re_render_Recall_screen ==
    /\ pc = "step_2"
    /\ pc' = "done"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out >>

\* --- Error actions ---
Step1_Capture_return_action_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out >>

Step2_Update_writing_flow_state_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out >>

Step3_Re_render_Recall_screen_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out >>

Next ==
    \/ Step1_Capture_return_action
    \/ Step2_Update_writing_flow_state
    \/ Step3_Re_render_Recall_screen
    \/ Step1_Capture_return_action_Error
    \/ Step2_Update_writing_flow_state_Error
    \/ Step3_Re_render_Recall_screen_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
