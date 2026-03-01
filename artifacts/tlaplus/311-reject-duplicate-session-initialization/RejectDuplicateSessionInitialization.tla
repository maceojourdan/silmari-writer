---- MODULE RejectDuplicateSessionInitialization ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS api_m5g7, api_n8k2, db_h2s4, db_d3w8, db_f8n5, db_j6x9, db_l1c3, api_q7v1

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
Step1_Receive_session_initialization_request ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out >>

Step2_Check_for_existing_active_session ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out >>

Step3_Validate_session_uniqueness_constraint ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out >>

Step4_Return_error_response_to_client ==
    /\ pc = "step_3"
    /\ pc' = "done"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out >>

\* --- Error actions ---
Step1_Receive_session_initialization_request_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step2_Check_for_existing_active_session_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step3_Validate_session_uniqueness_constraint_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step4_Return_error_response_to_client_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Next ==
    \/ Step1_Receive_session_initialization_request
    \/ Step2_Check_for_existing_active_session
    \/ Step3_Validate_session_uniqueness_constraint
    \/ Step4_Return_error_response_to_client
    \/ Step1_Receive_session_initialization_request_Error
    \/ Step2_Check_for_existing_active_session_Error
    \/ Step3_Validate_session_uniqueness_constraint_Error
    \/ Step4_Return_error_response_to_client_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
