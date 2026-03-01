---- MODULE FinalizeVoiceSessionAndPersistStoryrecord ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_w8p2, api_q7v1, api_m5g7, api_n8k2, db_h2s4, db_d3w8, db_f8n5, db_l1c3, cfg_j9w2, cfg_r3d7

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
Step1_Submit_finalize_session_request ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Validate_session_eligibility_for_finalization ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Update_session_state_to_FINALIZE ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out >>

Step4_Persist_StoryRecord_with_FINALIZED_status_and_responses ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out >>

Step5_Return_confirmation_response_to_user ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out >>

Step6_Display_finalized_session_state_in_UI ==
    /\ pc = "step_5"
    /\ pc' = "done"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

\* --- Error actions ---
Step1_Submit_finalize_session_request_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Validate_session_eligibility_for_finalization_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Update_session_state_to_FINALIZE_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step4_Persist_StoryRecord_with_FINALIZED_status_and_responses_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step5_Return_confirmation_response_to_user_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step6_Display_finalized_session_state_in_UI_Error ==
    /\ pc = "step_5"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Next ==
    \/ Step1_Submit_finalize_session_request
    \/ Step2_Validate_session_eligibility_for_finalization
    \/ Step3_Update_session_state_to_FINALIZE
    \/ Step4_Persist_StoryRecord_with_FINALIZED_status_and_responses
    \/ Step5_Return_confirmation_response_to_user
    \/ Step6_Display_finalized_session_state_in_UI
    \/ Step1_Submit_finalize_session_request_Error
    \/ Step2_Validate_session_eligibility_for_finalization_Error
    \/ Step3_Update_session_state_to_FINALIZE_Error
    \/ Step4_Persist_StoryRecord_with_FINALIZED_status_and_responses_Error
    \/ Step5_Return_confirmation_response_to_user_Error
    \/ Step6_Display_finalized_session_state_in_UI_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
