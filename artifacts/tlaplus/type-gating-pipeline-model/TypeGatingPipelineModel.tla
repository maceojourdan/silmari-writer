---- MODULE TypeGatingPipelineModel ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS fn_g1a1, fn_g1b2, fn_g1c3, fn_g2a4, fn_g2b5, cfg_w1s6, cfg_w1t7, cfg_w2s8, cfg_w2t9, api_r1p0

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
Step1_mime_resolved ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step2_frontend_gate_checked ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step3_content_converted ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step4_batch_iterated ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step5_request_serialized ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out, step_7_out, step_8_out >>

Step6_route_gate_checked ==
    /\ pc = "step_5"
    /\ pc' = "step_6"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_7_out, step_8_out >>

Step7_content_assembled ==
    /\ pc = "step_6"
    /\ pc' = "step_7"
    /\ step_7_out' = "step_7_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_8_out >>

Step8_delivered_to_llm ==
    /\ pc = "step_7"
    /\ pc' = "done"
    /\ step_8_out' = "step_8_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

\* --- Error actions ---
Step2_frontend_gate_checked_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step3_content_converted_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step4_batch_iterated_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step5_request_serialized_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Next ==
    \/ Step1_mime_resolved
    \/ Step2_frontend_gate_checked
    \/ Step3_content_converted
    \/ Step4_batch_iterated
    \/ Step5_request_serialized
    \/ Step6_route_gate_checked
    \/ Step7_content_assembled
    \/ Step8_delivered_to_llm
    \/ Step2_frontend_gate_checked_Error
    \/ Step3_content_converted_Error
    \/ Step4_batch_iterated_Error
    \/ Step5_request_serialized_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
