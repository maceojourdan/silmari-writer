---- MODULE PreventConfirmationWithoutSingleStorySelection ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_w8p2, ui_a4y1, ui_y5t3, cfg_j9w2, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "done", "error"}

ErrorConsistency ==
    error_state = TRUE => pc = "error"

Init ==
    /\ pc = "idle"
    /\ error_state = FALSE
    /\ step_1_out = "none"
    /\ step_2_out = "none"
    /\ step_3_out = "none"
    /\ step_4_out = "none"

\* --- Step actions ---
Step1_Capture_confirm_action ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out >>

Step2_Validate_single_selection_requirement ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out >>

Step3_Block_confirmation_flow ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out >>

Step4_Display_validation_feedback ==
    /\ pc = "step_3"
    /\ pc' = "done"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out >>

\* --- Error actions ---
Step1_Capture_confirm_action_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step2_Validate_single_selection_requirement_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step3_Block_confirmation_flow_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step4_Display_validation_feedback_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Next ==
    \/ Step1_Capture_confirm_action
    \/ Step2_Validate_single_selection_requirement
    \/ Step3_Block_confirmation_flow
    \/ Step4_Display_validation_feedback
    \/ Step1_Capture_confirm_action_Error
    \/ Step2_Validate_single_selection_requirement_Error
    \/ Step3_Block_confirmation_flow_Error
    \/ Step4_Display_validation_feedback_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
