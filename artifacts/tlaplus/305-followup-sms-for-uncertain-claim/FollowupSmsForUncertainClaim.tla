---- MODULE FollowupSmsForUncertainClaim ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS mq_t2f7, mq_u6j3, mq_r4z8, db_d3w8, db_f8n5, db_h2s4, db_b7r2, db_l1c3, api_m5g7, api_n8k2, cfg_h5v9, cfg_m2z6, cfg_p4b8, cfg_q9c5, cfg_j9w2

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
Step1_Trigger_FOLLOWUP_SMS_pattern ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Validate_claim_eligibility ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out >>

Step3_Send_follow_up_SMS ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out >>

Step4_Receive_SMS_reply_webhook ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out >>

Step5_Update_truth_checks_record ==
    /\ pc = "step_4"
    /\ pc' = "done"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out >>

\* --- Error actions ---
Step1_Trigger_FOLLOWUP_SMS_pattern_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Validate_claim_eligibility_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step3_Send_follow_up_SMS_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step4_Receive_SMS_reply_webhook_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step5_Update_truth_checks_record_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Next ==
    \/ Step1_Trigger_FOLLOWUP_SMS_pattern
    \/ Step2_Validate_claim_eligibility
    \/ Step3_Send_follow_up_SMS
    \/ Step4_Receive_SMS_reply_webhook
    \/ Step5_Update_truth_checks_record
    \/ Step1_Trigger_FOLLOWUP_SMS_pattern_Error
    \/ Step2_Validate_claim_eligibility_Error
    \/ Step3_Send_follow_up_SMS_Error
    \/ Step4_Receive_SMS_reply_webhook_Error
    \/ Step5_Update_truth_checks_record_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
