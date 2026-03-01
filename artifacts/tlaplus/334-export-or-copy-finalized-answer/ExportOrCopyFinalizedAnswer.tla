---- MODULE ExportOrCopyFinalizedAnswer ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_v3n6, ui_w8p2, ui_y5t3, api_q7v1, api_m5g7, api_n8k2, db_h2s4, db_d3w8, db_f8n5, db_j6x9, db_l1c3, cfg_h5v9, cfg_f7s8, cfg_j9w2, cfg_r3d7

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
Step1_Capture_export_or_copy_action ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out >>

Step2_Load_finalized_answer_content ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out >>

Step3_Transform_content_to_selected_export_format ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out >>

Step4_Deliver_export_or_copy_result_to_user ==
    /\ pc = "step_3"
    /\ pc' = "done"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out >>

\* --- Error actions ---
Step1_Capture_export_or_copy_action_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step2_Load_finalized_answer_content_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step3_Transform_content_to_selected_export_format_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step4_Deliver_export_or_copy_result_to_user_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Next ==
    \/ Step1_Capture_export_or_copy_action
    \/ Step2_Load_finalized_answer_content
    \/ Step3_Transform_content_to_selected_export_format
    \/ Step4_Deliver_export_or_copy_result_to_user
    \/ Step1_Capture_export_or_copy_action_Error
    \/ Step2_Load_finalized_answer_content_Error
    \/ Step3_Transform_content_to_selected_export_format_Error
    \/ Step4_Deliver_export_or_copy_result_to_user_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
