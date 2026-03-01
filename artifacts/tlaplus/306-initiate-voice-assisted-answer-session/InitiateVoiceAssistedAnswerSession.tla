---- MODULE InitiateVoiceAssistedAnswerSession ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ui_v3n6, ui_x1r9, api_q7v1, api_m5g7, api_p3e6, api_n8k2, db_h2s4, db_d3w8, db_f8n5, db_l1c3, cfg_j9w2, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "step_5", "step_6", "step_7", "done", "error"}

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

\* --- Step actions ---
Step1_User_initiates_voice_session ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step2_API_endpoint_receives_session_creation_request ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step3_Request_handler_invokes_session_initialization_logic ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step4_Service_creates_Answer_Session_in_INIT_state ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out, step_7_out >>

Step5_Service_creates_corresponding_StoryRecord_in_INIT_status ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out, step_7_out >>

Step6_Return_session_initialization_response_to_frontend ==
    /\ pc = "step_5"
    /\ pc' = "step_6"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_7_out >>

Step7_Frontend_renders_voice_assisted_session_interface ==
    /\ pc = "step_6"
    /\ pc' = "done"
    /\ step_7_out' = "step_7_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

\* --- Error actions ---
Step1_User_initiates_voice_session_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step2_API_endpoint_receives_session_creation_request_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step3_Request_handler_invokes_session_initialization_logic_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step4_Service_creates_Answer_Session_in_INIT_state_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step5_Service_creates_corresponding_StoryRecord_in_INIT_status_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step6_Return_session_initialization_response_to_frontend_Error ==
    /\ pc = "step_5"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Step7_Frontend_renders_voice_assisted_session_interface_Error ==
    /\ pc = "step_6"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

Next ==
    \/ Step1_User_initiates_voice_session
    \/ Step2_API_endpoint_receives_session_creation_request
    \/ Step3_Request_handler_invokes_session_initialization_logic
    \/ Step4_Service_creates_Answer_Session_in_INIT_state
    \/ Step5_Service_creates_corresponding_StoryRecord_in_INIT_status
    \/ Step6_Return_session_initialization_response_to_frontend
    \/ Step7_Frontend_renders_voice_assisted_session_interface
    \/ Step1_User_initiates_voice_session_Error
    \/ Step2_API_endpoint_receives_session_creation_request_Error
    \/ Step3_Request_handler_invokes_session_initialization_logic_Error
    \/ Step4_Service_creates_Answer_Session_in_INIT_state_Error
    \/ Step5_Service_creates_corresponding_StoryRecord_in_INIT_status_Error
    \/ Step6_Return_session_initialization_response_to_frontend_Error
    \/ Step7_Frontend_renders_voice_assisted_session_interface_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
