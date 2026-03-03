---- MODULE UrlIngestionErrorSpaceModel ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS api_e5f6, api_n8k2, db_h2s4, db_d3w8, db_g9p1, cfg_v2t5, db_k4m7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "step_5", "step_6", "step_7", "step_8", "done", "error"}

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
    /\ step_8_out = "none"

\* --- Step actions ---
Step1_Receive_and_validate_URL_submission ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step2_Check_active_session_uniqueness ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step3_Finalize_stale_zombie_session_Fix_4__new_sub_step ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step4_Persist_session_to_database ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step5_Return_success_response_to_client ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out, step_7_out, step_8_out >>

Step6_Load_session_page ==
    /\ pc = "step_5"
    /\ pc' = "step_6"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_7_out, step_8_out >>

Step7_Validate_session_view_response ==
    /\ pc = "step_6"
    /\ pc' = "step_7"
    /\ step_7_out' = "step_7_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_8_out >>

Step8_User_retry__recovery_or_blocked ==
    /\ pc = "step_7"
    /\ pc' = "done"
    /\ step_8_out' = "step_8_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

\* --- Error actions ---
Step1_Receive_and_validate_URL_submission_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step2_Check_active_session_uniqueness_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step3_Finalize_stale_zombie_session_Fix_4__new_sub_step_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step4_Persist_session_to_database_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step5_Return_success_response_to_client_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step7_Validate_session_view_response_Error ==
    /\ pc = "step_6"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step8_User_retry__recovery_or_blocked_Error ==
    /\ pc = "step_7"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Next ==
    \/ Step1_Receive_and_validate_URL_submission
    \/ Step2_Check_active_session_uniqueness
    \/ Step3_Finalize_stale_zombie_session_Fix_4__new_sub_step
    \/ Step4_Persist_session_to_database
    \/ Step5_Return_success_response_to_client
    \/ Step6_Load_session_page
    \/ Step7_Validate_session_view_response
    \/ Step8_User_retry__recovery_or_blocked
    \/ Step1_Receive_and_validate_URL_submission_Error
    \/ Step2_Check_active_session_uniqueness_Error
    \/ Step3_Finalize_stale_zombie_session_Fix_4__new_sub_step_Error
    \/ Step4_Persist_session_to_database_Error
    \/ Step5_Return_success_response_to_client_Error
    \/ Step7_Validate_session_view_response_Error
    \/ Step8_User_retry__recovery_or_blocked_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
