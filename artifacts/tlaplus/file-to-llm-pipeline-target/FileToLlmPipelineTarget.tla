---- MODULE FileToLlmPipelineTarget ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_w8p2, ui_v3n6, ui_y5t3, api_q7v1, api_m5g7, cfg_f7s8, MAX_RETRIES_1

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "step_5", "step_6", "step_7", "step_8", "step_9", "step_10", "step_11", "done", "error"}

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
    /\ step_9_out = "none"
    /\ step_10_out = "none"
    /\ step_11_out = "none"
    /\ retry_counter_1 = 0

\* --- Step actions ---
Step1_files_selected ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step2_message_submitted ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step3_guard_check ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step4_user_msg_stored ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step5_file_content_prepared ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step6_generating ==
    /\ pc = "step_5"
    /\ pc' = "step_6"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step7_openai_messages_built ==
    /\ pc = "step_6"
    /\ pc' = "step_7"
    /\ step_7_out' = "step_7_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step8_openai_calling ==
    /\ pc = "step_7"
    /\ pc' = "step_8"
    /\ step_8_out' = "step_8_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step9_response_received ==
    /\ pc = "step_8"
    /\ pc' = "step_9"
    /\ step_9_out' = "step_9_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_10_out, step_11_out, retry_counter_1 >>

Step10_assistant_msg_stored ==
    /\ pc = "step_9"
    /\ pc' = "step_10"
    /\ step_10_out' = "step_10_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_11_out, retry_counter_1 >>

Step11_files_cleared ==
    /\ pc = "step_10"
    /\ pc' = "done"
    /\ step_11_out' = "step_11_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, retry_counter_1 >>

\* --- Error actions ---
Step1_files_selected_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step2_message_submitted_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step4_user_msg_stored_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step5_file_content_prepared_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step6_generating_Error ==
    /\ pc = "step_5"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step7_openai_messages_built_Error ==
    /\ pc = "step_6"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step8_openai_calling_Error ==
    /\ pc = "step_7"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Step9_response_received_Error ==
    /\ pc = "step_8"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out, step_9_out, step_10_out, step_11_out, retry_counter_1 >>

Next ==
    \/ Step1_files_selected
    \/ Step2_message_submitted
    \/ Step3_guard_check
    \/ Step4_user_msg_stored
    \/ Step5_file_content_prepared
    \/ Step6_generating
    \/ Step7_openai_messages_built
    \/ Step8_openai_calling
    \/ Step9_response_received
    \/ Step10_assistant_msg_stored
    \/ Step11_files_cleared
    \/ Step1_files_selected_Error
    \/ Step2_message_submitted_Error
    \/ Step4_user_msg_stored_Error
    \/ Step5_file_content_prepared_Error
    \/ Step6_generating_Error
    \/ Step7_openai_messages_built_Error
    \/ Step8_openai_calling_Error
    \/ Step9_response_received_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
