---- MODULE CompleteVoiceAnswerAdvancesWorkflow ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS cfg_d2q3, cfg_h5v9, cfg_g1u4, cfg_j9w2, db_h2s4, db_d3w8, db_l1c3, mq_r4z8, ui_w8p2, cfg_r3d7

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
Step1_Capture_spoken_answer ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Extract_slot_values_from_response ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Validate_minimum_required_slots ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out >>

Step4_Persist_completed_slot_set ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out >>

Step5_Advance_workflow_to_next_step ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out >>

Step6_Deliver_next_prompt_to_user ==
    /\ pc = "step_5"
    /\ pc' = "done"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

\* --- Error actions ---
Step1_Capture_spoken_answer_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Extract_slot_values_from_response_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Validate_minimum_required_slots_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step4_Persist_completed_slot_set_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step5_Advance_workflow_to_next_step_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step6_Deliver_next_prompt_to_user_Error ==
    /\ pc = "step_5"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Next ==
    \/ Step1_Capture_spoken_answer
    \/ Step2_Extract_slot_values_from_response
    \/ Step3_Validate_minimum_required_slots
    \/ Step4_Persist_completed_slot_set
    \/ Step5_Advance_workflow_to_next_step
    \/ Step6_Deliver_next_prompt_to_user
    \/ Step1_Capture_spoken_answer_Error
    \/ Step2_Extract_slot_values_from_response_Error
    \/ Step3_Validate_minimum_required_slots_Error
    \/ Step4_Persist_completed_slot_set_Error
    \/ Step5_Advance_workflow_to_next_step_Error
    \/ Step6_Deliver_next_prompt_to_user_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
