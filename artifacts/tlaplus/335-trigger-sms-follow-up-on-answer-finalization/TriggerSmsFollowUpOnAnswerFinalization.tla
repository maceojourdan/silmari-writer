---- MODULE TriggerSmsFollowUpOnAnswerFinalization ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS mq_r4z8, db_f8n5, db_d3w8, db_l1c3, cfg_j9w2, cfg_m2z6, cfg_q9c5

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
Step1_Detect_Finalize_Completion_Event ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Load_Answer_and_Contact_Data ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out >>

Step3_Compose_SMS_Follow_up_Message ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out >>

Step4_Send_SMS_via_External_Provider ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out >>

Step5_Record_SMS_Dispatch_Result ==
    /\ pc = "step_4"
    /\ pc' = "done"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out >>

\* --- Error actions ---
Step1_Detect_Finalize_Completion_Event_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Load_Answer_and_Contact_Data_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step3_Compose_SMS_Follow_up_Message_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step4_Send_SMS_via_External_Provider_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step5_Record_SMS_Dispatch_Result_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Next ==
    \/ Step1_Detect_Finalize_Completion_Event
    \/ Step2_Load_Answer_and_Contact_Data
    \/ Step3_Compose_SMS_Follow_up_Message
    \/ Step4_Send_SMS_via_External_Provider
    \/ Step5_Record_SMS_Dispatch_Result
    \/ Step1_Detect_Finalize_Completion_Event_Error
    \/ Step2_Load_Answer_and_Contact_Data_Error
    \/ Step3_Compose_SMS_Follow_up_Message_Error
    \/ Step4_Send_SMS_via_External_Provider_Error
    \/ Step5_Record_SMS_Dispatch_Result_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
