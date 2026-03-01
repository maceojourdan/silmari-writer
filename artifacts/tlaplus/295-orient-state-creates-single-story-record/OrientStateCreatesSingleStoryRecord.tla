---- MODULE OrientStateCreatesSingleStoryRecord ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS mq_r4z8, db_f8n5, db_j6x9, db_d3w8, api_n8k2, db_l1c3

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
Step1_Trigger_ORIENT_process_chain ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Select_single_experience_and_derive_story_data ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out >>

Step3_Validate_StoryRecord_structure ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out >>

Step4_Persist_StoryRecord ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out >>

Step5_Return_StoryRecord_to_interface ==
    /\ pc = "step_4"
    /\ pc' = "done"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out >>

\* --- Error actions ---
Step1_Trigger_ORIENT_process_chain_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Select_single_experience_and_derive_story_data_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step3_Validate_StoryRecord_structure_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step4_Persist_StoryRecord_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step5_Return_StoryRecord_to_interface_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Next ==
    \/ Step1_Trigger_ORIENT_process_chain
    \/ Step2_Select_single_experience_and_derive_story_data
    \/ Step3_Validate_StoryRecord_structure
    \/ Step4_Persist_StoryRecord
    \/ Step5_Return_StoryRecord_to_interface
    \/ Step1_Trigger_ORIENT_process_chain_Error
    \/ Step2_Select_single_experience_and_derive_story_data_Error
    \/ Step3_Validate_StoryRecord_structure_Error
    \/ Step4_Persist_StoryRecord_Error
    \/ Step5_Return_StoryRecord_to_interface_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
