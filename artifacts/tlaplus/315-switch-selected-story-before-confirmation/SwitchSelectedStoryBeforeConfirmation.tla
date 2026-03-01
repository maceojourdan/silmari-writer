---- MODULE SwitchSelectedStoryBeforeConfirmation ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_w8p2, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "done", "error"}

ErrorConsistency ==
    error_state = TRUE => pc = "error"

Init ==
    /\ pc = "idle"
    /\ error_state = FALSE
    /\ step_1_out = "none"
    /\ step_2_out = "none"
    /\ step_3_out = "none"
    /\ step_4_out = "none"

\* --- Step actions ---
Step1_Capture_story_selection_event ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out >>

Step2_Evaluate_selection_change ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out >>

Step3_Update_selected_story_state ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out >>

Step4_Render_updated_selection_in_UI ==
    /\ pc = "step_3"
    /\ pc' = "done"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out >>

\* --- Error actions ---
Step1_Capture_story_selection_event_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step2_Evaluate_selection_change_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step3_Update_selected_story_state_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step4_Render_updated_selection_in_UI_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Next ==
    \/ Step1_Capture_story_selection_event
    \/ Step2_Evaluate_selection_change
    \/ Step3_Update_selected_story_state
    \/ Step4_Render_updated_selection_in_UI
    \/ Step1_Capture_story_selection_event_Error
    \/ Step2_Evaluate_selection_change_Error
    \/ Step3_Update_selected_story_state_Error
    \/ Step4_Render_updated_selection_in_UI_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
