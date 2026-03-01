---- MODULE VerificationTimeoutKeepsClaimsUnverifiedAndDraftingOnHold ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS cfg_l8y1, db_f8n5, db_d3w8, db_h2s4, db_j6x9, db_l1c3, api_m5g7, api_n8k2, ui_y5t3, ui_v3n6, ui_w8p2, cfg_q9c5, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "step_5", "done", "error"}

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

\* --- Step actions ---
Step1_Detect_verification_timeout_event ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Update_verification_status_to_timed_out ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out >>

Step3_Enforce_claims_remain_unverified_and_drafting_on_hold ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out >>

Step4_Expose_updated_status_to_frontend ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out >>

Step5_Render_timeout_state_in_drafting_UI ==
    /\ pc = "step_4"
    /\ pc' = "done"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out >>

\* --- Error actions ---
Step1_Detect_verification_timeout_event_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Update_verification_status_to_timed_out_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step3_Enforce_claims_remain_unverified_and_drafting_on_hold_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step4_Expose_updated_status_to_frontend_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step5_Render_timeout_state_in_drafting_UI_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Next ==
    \/ Step1_Detect_verification_timeout_event
    \/ Step2_Update_verification_status_to_timed_out
    \/ Step3_Enforce_claims_remain_unverified_and_drafting_on_hold
    \/ Step4_Expose_updated_status_to_frontend
    \/ Step5_Render_timeout_state_in_drafting_UI
    \/ Step1_Detect_verification_timeout_event_Error
    \/ Step2_Update_verification_status_to_timed_out_Error
    \/ Step3_Enforce_claims_remain_unverified_and_drafting_on_hold_Error
    \/ Step4_Expose_updated_status_to_frontend_Error
    \/ Step5_Render_timeout_state_in_drafting_UI_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
