---- MODULE CopyArtifactToClipboard ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_a2b3, ui_c4d5, cfg_j9w2, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "done", "error"}

ErrorConsistency ==
    error_state = TRUE => pc = "error"

Init ==
    /\ pc = "idle"
    /\ error_state = FALSE
    /\ step_1_out = "none"
    /\ step_2_out = "none"
    /\ step_3_out = "none"

\* --- Step actions ---
Step1_Render_artifact_with_Copy_button ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out >>

Step2_Execute_clipboard_write ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out >>

Step3_Provide_immediate_visual_confirmation ==
    /\ pc = "step_2"
    /\ pc' = "done"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out >>

\* --- Error actions ---
Step1_Render_artifact_with_Copy_button_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out >>

Step2_Execute_clipboard_write_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out >>

Next ==
    \/ Step1_Render_artifact_with_Copy_button
    \/ Step2_Execute_clipboard_write
    \/ Step3_Provide_immediate_visual_confirmation
    \/ Step1_Render_artifact_with_Copy_button_Error
    \/ Step2_Execute_clipboard_write_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
