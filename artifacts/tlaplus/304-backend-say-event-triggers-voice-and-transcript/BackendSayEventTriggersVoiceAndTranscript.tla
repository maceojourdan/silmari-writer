---- MODULE BackendSayEventTriggersVoiceAndTranscript ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS mq_r4z8, db_j6x9, cfg_h5v9, cfg_j9w2, cfg_q9c5, ui_v3n6, ui_a4y1, cfg_r3d7

VARIABLES pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out

vars == << pc, error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

TypeInvariant ==
    pc \in {"idle", "step_1", "step_2", "step_3", "step_4", "step_5", "step_6", "done", "error"}

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

\* --- Step actions ---
Step1_Intercept_SAY_event ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "step_1_result"
    /\ UNCHANGED << error_state, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Validate_session_context ==
    /\ pc = "step_1"
    /\ pc' = "step_2"
    /\ step_2_out' = "step_2_result"
    /\ UNCHANGED << error_state, step_1_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Transform_prompt_to_speech_request ==
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ step_3_out' = "step_3_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_4_out, step_5_out, step_6_out >>

Step4_Synthesize_and_stream_audio ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "step_4_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_5_out, step_6_out >>

Step5_Emit_TRANSCRIPT_FINAL_event ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "step_5_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_6_out >>

Step6_Render_transcript_in_UI ==
    /\ pc = "step_5"
    /\ pc' = "done"
    /\ step_6_out' = "step_6_result"
    /\ UNCHANGED << error_state, step_1_out, step_2_out, step_3_out, step_4_out, step_5_out >>

\* --- Error actions ---
Step1_Intercept_SAY_event_Error ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step2_Validate_session_context_Error ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step3_Transform_prompt_to_speech_request_Error ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step4_Synthesize_and_stream_audio_Error ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step5_Emit_TRANSCRIPT_FINAL_event_Error ==
    /\ pc = "step_4"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Step6_Render_transcript_in_UI_Error ==
    /\ pc = "step_5"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ UNCHANGED << step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out >>

Next ==
    \/ Step1_Intercept_SAY_event
    \/ Step2_Validate_session_context
    \/ Step3_Transform_prompt_to_speech_request
    \/ Step4_Synthesize_and_stream_audio
    \/ Step5_Emit_TRANSCRIPT_FINAL_event
    \/ Step6_Render_transcript_in_UI
    \/ Step1_Intercept_SAY_event_Error
    \/ Step2_Validate_session_context_Error
    \/ Step3_Transform_prompt_to_speech_request_Error
    \/ Step4_Synthesize_and_stream_audio_Error
    \/ Step5_Emit_TRANSCRIPT_FINAL_event_Error
    \/ Step6_Render_transcript_in_UI_Error
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* --- Properties ---
Reachability == <>(pc \in {"done", "error"})

====
