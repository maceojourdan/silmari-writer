---- MODULE LinkedinContentPlanningWorkflow ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_a1b1, ui_c2d2, api_e3f3, db_h2s4, db_d3w8, db_l1c3, cfg_r3d7

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
Step1_Select_company_and_contribution_areas_for_LinkedIn_content ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out >>

Step2_Generate_LinkedIn_post_drafts ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out >>

Step3_Display_drafts_with_manual_post_only_safeguard ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out >>

Step4_User_copies_draft_to_clipboard ==
    /\ pc = "step_3"
    /\ pc' = "done"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out >>

\* --- Error actions ---
Step1_Select_company_and_contribution_areas_for_LinkedIn_content_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step2_Generate_LinkedIn_post_drafts_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Step4_User_copies_draft_to_clipboard_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out >>

Next ==
    \/ Step1_Select_company_and_contribution_areas_for_LinkedIn_content
    \/ Step2_Generate_LinkedIn_post_drafts
    \/ Step3_Display_drafts_with_manual_post_only_safeguard
    \/ Step4_User_copies_draft_to_clipboard
    \/ Step1_Select_company_and_contribution_areas_for_LinkedIn_content_Error
    \/ Step2_Generate_LinkedIn_post_drafts_Error
    \/ Step4_User_copies_draft_to_clipboard_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
