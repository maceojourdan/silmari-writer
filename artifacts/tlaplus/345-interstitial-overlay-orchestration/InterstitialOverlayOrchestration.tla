---- MODULE InterstitialOverlayOrchestration ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_h1i2, ui_j3k4, ui_l5m6, cfg_r3d7, cfg_j9w2

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
Step1_Detect_stage_transition ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Show_interstitial_overlay ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out >>

Step3_Track_dwell_and_dismissal ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out >>

Step4_Handle_abandonment ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out >>

Step5_Advance_to_next_stage ==
    /\ pc = "step_4"
    /\ pc' = "done"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out >>

\* --- Error actions ---
Step1_Detect_stage_transition_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step2_Show_interstitial_overlay_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step4_Handle_abandonment_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Step5_Advance_to_next_stage_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

Next ==
    \/ Step1_Detect_stage_transition
    \/ Step2_Show_interstitial_overlay
    \/ Step3_Track_dwell_and_dismissal
    \/ Step4_Handle_abandonment
    \/ Step5_Advance_to_next_stage
    \/ Step1_Detect_stage_transition_Error
    \/ Step2_Show_interstitial_overlay_Error
    \/ Step4_Handle_abandonment_Error
    \/ Step5_Advance_to_next_stage_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
