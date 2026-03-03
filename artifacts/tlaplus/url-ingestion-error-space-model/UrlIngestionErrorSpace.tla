---- MODULE UrlIngestionErrorSpace ----
EXTENDS Naturals, Sequences, FiniteSets

\* Resource constants (from path spec)
CONSTANTS api_e5f6, api_n8k2, db_h2s4, db_d3w8, db_g9p1, cfg_v2t5, db_k4m7

\* Mode selector: "buggy" or "fixed"
\* When mode = "fixed", only fixed transitions are enabled.
\* When mode = "buggy", only buggy transitions are enabled.
CONSTANTS mode

\* State variables
VARIABLES pc, error_state, error_code,
          session_persisted, updated_at_is_null,
          zombie_session_exists, session_view_valid,
          \* Fix 3 variables: user-scoped uniqueness
          current_user, session_owner,
          \* Fix 4 variables: zombie cleanup
          zombie_age_stale, zombie_superseded,
          \* Fix 2 variables: nullable schema
          schema_accepts_null_updated_at,
          \* Step outputs
          step_1_out, step_2_out, step_3_out, step_4_out,
          step_5_out, step_6_out, step_7_out, step_8_out

vars == << pc, error_state, error_code,
           session_persisted, updated_at_is_null,
           zombie_session_exists, session_view_valid,
           current_user, session_owner,
           zombie_age_stale, zombie_superseded,
           schema_accepts_null_updated_at,
           step_1_out, step_2_out, step_3_out, step_4_out,
           step_5_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* TYPE INVARIANT
\* ====================================================================
TypeInvariant ==
    /\ pc \in {"idle", "step_1", "step_2", "step_2b", "step_3", "step_4",
               "step_5", "step_6", "step_7", "step_8",
               "done", "error", "blocked"}
    /\ error_state \in {TRUE, FALSE}
    /\ error_code \in {"none", "INVALID_REQUEST", "AUTH_FAILURE",
                        "SESSION_ALREADY_ACTIVE", "PERSISTENCE_FAILURE",
                        "INTERNAL_ERROR", "SCHEMA_VALIDATION_FAILED"}
    /\ session_persisted \in {TRUE, FALSE}
    /\ updated_at_is_null \in {TRUE, FALSE}
    /\ zombie_session_exists \in {TRUE, FALSE}
    /\ session_view_valid \in {TRUE, FALSE}
    /\ current_user \in {"user_a", "user_b", "none"}
    /\ session_owner \in {"user_a", "user_b", "none"}
    /\ zombie_age_stale \in {TRUE, FALSE}
    /\ zombie_superseded \in {TRUE, FALSE}
    /\ schema_accepts_null_updated_at \in {TRUE, FALSE}
    /\ mode \in {"buggy", "fixed"}

\* ====================================================================
\* ERROR CONSISTENCY
\* ====================================================================
ErrorConsistency ==
    (pc = "error" \/ pc = "blocked") => error_state = TRUE

\* ====================================================================
\* INVARIANTS — must hold in "fixed" mode, expected to fail in "buggy"
\* ====================================================================

\* INV-1: Persisted session must be loadable
\* In fixed mode, persist sets updated_at, so schema validation passes
PersistedSessionLoadable ==
    (mode = "fixed" /\ session_persisted = TRUE) => <>(pc = "done")

\* INV-2: updated_at must be non-null after persist
UpdatedAtNonNull ==
    (mode = "fixed" /\ session_persisted = TRUE) => updated_at_is_null = FALSE

\* INV-3: Active session check must be user-scoped
\* In fixed mode, user_a's zombie does not block user_b
UserScopedUniqueness ==
    (mode = "fixed" /\ zombie_session_exists = TRUE /\ session_owner = "user_a" /\ current_user = "user_b")
        => pc /= "blocked"

\* INV-4: Zombie sessions are recoverable (cleanup or supersede)
\* In fixed mode, stale zombies get superseded — system never reaches permanent "blocked"
ZombieRecoverable ==
    (mode = "fixed") => [](pc /= "blocked")

\* INV-5: Write-read consistency — persist success implies read success
WriteReadConsistency ==
    (mode = "fixed" /\ session_persisted = TRUE /\ pc = "step_6") => session_view_valid = TRUE

\* INV-6: Observability — not modeled at state level (test oracle only)

\* ====================================================================
\* INIT
\* ====================================================================
Init ==
    /\ pc = "idle"
    /\ error_state = FALSE
    /\ error_code = "none"
    /\ session_persisted = FALSE
    /\ updated_at_is_null = FALSE
    /\ zombie_session_exists = FALSE
    /\ session_view_valid = FALSE
    /\ current_user = "user_a"
    /\ session_owner = "none"
    /\ zombie_age_stale = FALSE
    /\ zombie_superseded = FALSE
    /\ schema_accepts_null_updated_at = (mode = "fixed")
    /\ step_1_out = "none"
    /\ step_2_out = "none"
    /\ step_3_out = "none"
    /\ step_4_out = "none"
    /\ step_5_out = "none"
    /\ step_6_out = "none"
    /\ step_7_out = "none"
    /\ step_8_out = "none"

\* ====================================================================
\* STEP 1: Receive and validate URL submission
\* (Identical in buggy and fixed versions)
\* ====================================================================
Step1_ValidateUrl ==
    /\ pc = "idle"
    /\ pc' = "step_1"
    /\ step_1_out' = "validated_url"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step1_Error_InvalidRequest ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "INVALID_REQUEST"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step1_Error_Auth ==
    /\ pc = "idle"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "AUTH_FAILURE"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* STEP 2: Check active session uniqueness
\* BUGGY: global check — any initialized session blocks everyone
\* FIXED: user-scoped check — only current_user's own session blocks
\* ====================================================================

\* --- Buggy: global check, no zombie in table ---
Step2_Buggy_NoActiveSession ==
    /\ mode = "buggy"
    /\ pc = "step_1"
    /\ zombie_session_exists = FALSE
    /\ pc' = "step_2"
    /\ step_2_out' = "uniqueness_passed"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* --- Buggy: global check, zombie exists — blocks any user ---
Step2_Buggy_ZombieBlocks ==
    /\ mode = "buggy"
    /\ pc = "step_1"
    /\ zombie_session_exists = TRUE
    /\ pc' = "blocked"
    /\ error_state' = TRUE
    /\ error_code' = "SESSION_ALREADY_ACTIVE"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* --- Fixed: user-scoped check, no active session for this user ---
Step2_Fixed_NoActiveForUser ==
    /\ mode = "fixed"
    /\ pc = "step_1"
    /\ \/ zombie_session_exists = FALSE
       \/ (zombie_session_exists = TRUE /\ session_owner /= current_user)
    /\ pc' = "step_2"
    /\ step_2_out' = "uniqueness_passed_user_scoped"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* --- Fixed: user's own session exists but is stale — supersede it (Fix 4) ---
Step2_Fixed_SupersedeStaleZombie ==
    /\ mode = "fixed"
    /\ pc = "step_1"
    /\ zombie_session_exists = TRUE
    /\ session_owner = current_user
    /\ zombie_age_stale = TRUE
    /\ pc' = "step_2b"
    /\ zombie_superseded' = TRUE
    /\ step_2_out' = "stale_zombie_superseded"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale,
                    schema_accepts_null_updated_at,
                    step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* --- Fixed: user's own fresh session exists — legitimate block ---
Step2_Fixed_OwnFreshSessionBlocks ==
    /\ mode = "fixed"
    /\ pc = "step_1"
    /\ zombie_session_exists = TRUE
    /\ session_owner = current_user
    /\ zombie_age_stale = FALSE
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "SESSION_ALREADY_ACTIVE"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* --- Shared: DB failure on uniqueness check ---
Step2_Error_Persistence ==
    /\ pc = "step_1"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "PERSISTENCE_FAILURE"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* STEP 2B: Finalize stale zombie before creating new session (Fix 4)
\* Transitions stale zombie to 'ended' state, then proceeds to persist
\* ====================================================================
Step2b_FinalizeStaleZombie ==
    /\ pc = "step_2b"
    /\ zombie_session_exists' = FALSE    \* Zombie marked ended, no longer active
    /\ zombie_age_stale' = FALSE
    /\ pc' = "step_2"
    /\ step_2_out' = "zombie_finalized"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    session_view_valid,
                    current_user, session_owner, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step2b_Error_FinalizeFails ==
    /\ pc = "step_2b"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "PERSISTENCE_FAILURE"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* STEP 3: Persist session to database
\* BUGGY: does not set updated_at — leaves NULL
\* FIXED: sets updated_at = createdAt at insert time
\* ====================================================================

\* --- Buggy: persist without updated_at ---
Step3_Persist_Buggy ==
    /\ mode = "buggy"
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ session_persisted' = TRUE
    /\ updated_at_is_null' = TRUE           \* <-- THE BUG
    /\ zombie_session_exists' = TRUE
    /\ session_owner' = current_user
    /\ step_3_out' = "persisted_without_updated_at"
    /\ UNCHANGED << error_state, error_code, session_view_valid,
                    current_user, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* --- Fixed: persist WITH updated_at = createdAt ---
Step3_Persist_Fixed ==
    /\ mode = "fixed"
    /\ pc = "step_2"
    /\ pc' = "step_3"
    /\ session_persisted' = TRUE
    /\ updated_at_is_null' = FALSE          \* <-- FIX 1: updated_at set
    /\ zombie_session_exists' = TRUE
    /\ session_owner' = current_user
    /\ step_3_out' = "persisted_with_updated_at"
    /\ UNCHANGED << error_state, error_code, session_view_valid,
                    current_user, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* --- Shared: DB insert failure ---
Step3_Error_DbInsert ==
    /\ pc = "step_2"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "PERSISTENCE_FAILURE"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* STEP 4: Return success response to client
\* (Identical in buggy and fixed)
\* ====================================================================
Step4_ApiSuccess ==
    /\ pc = "step_3"
    /\ pc' = "step_4"
    /\ step_4_out' = "success_response"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_5_out, step_6_out, step_7_out, step_8_out >>

Step4_Error_ResponseValidation ==
    /\ pc = "step_3"
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "INTERNAL_ERROR"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* STEP 5: Load session page (GET /api/sessions/[id])
\* (Identical in buggy and fixed)
\* ====================================================================
Step5_LoadSession ==
    /\ pc = "step_4"
    /\ pc' = "step_5"
    /\ step_5_out' = "session_row_loaded"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* STEP 6: Validate SessionView schema
\* BUGGY: updatedAt: z.string() — rejects null
\* FIXED: updatedAt: z.string().nullable() — accepts null (Fix 2)
\*        AND updated_at is never null anyway (Fix 1)
\* ====================================================================

\* --- Schema passes: updated_at is non-null ---
Step6_SchemaValid_NonNull ==
    /\ pc = "step_5"
    /\ updated_at_is_null = FALSE
    /\ pc' = "done"
    /\ session_view_valid' = TRUE
    /\ step_6_out' = "schema_valid"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_7_out, step_8_out >>

\* --- Fixed (Fix 2): Schema passes even when updated_at is null (defense-in-depth) ---
Step6_Fixed_SchemaAcceptsNull ==
    /\ mode = "fixed"
    /\ pc = "step_5"
    /\ updated_at_is_null = TRUE
    /\ schema_accepts_null_updated_at = TRUE
    /\ pc' = "done"
    /\ session_view_valid' = TRUE
    /\ step_6_out' = "schema_valid_null_tolerated"
    /\ UNCHANGED << error_state, error_code, session_persisted, updated_at_is_null,
                    zombie_session_exists,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_7_out, step_8_out >>

\* --- Buggy: Schema rejects null updated_at ---
Step6_Buggy_SchemaFails ==
    /\ mode = "buggy"
    /\ pc = "step_5"
    /\ updated_at_is_null = TRUE
    /\ pc' = "error"
    /\ error_state' = TRUE
    /\ error_code' = "SCHEMA_VALIDATION_FAILED"
    /\ session_view_valid' = FALSE
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out, step_8_out >>

\* ====================================================================
\* STEP 7: User retry (buggy path — blocked by zombie)
\* Only reachable in buggy mode after schema validation failure
\* ====================================================================
Step7_Buggy_RetryBlocked ==
    /\ mode = "buggy"
    /\ pc = "error"
    /\ error_code = "SCHEMA_VALIDATION_FAILED"
    /\ zombie_session_exists = TRUE
    /\ pc' = "blocked"
    /\ error_code' = "SESSION_ALREADY_ACTIVE"
    /\ step_7_out' = "retry_blocked_permanently"
    /\ UNCHANGED << error_state, session_persisted, updated_at_is_null,
                    zombie_session_exists, session_view_valid,
                    current_user, session_owner, zombie_age_stale, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_8_out >>

\* ====================================================================
\* STEP 8: User retry (fixed path — succeeds via supersede or clean state)
\* In fixed mode, retry after any recoverable error re-enters from idle
\* ====================================================================
Step8_Fixed_RetrySucceeds ==
    /\ mode = "fixed"
    /\ pc = "error"
    /\ pc' = "idle"
    /\ error_state' = FALSE
    /\ error_code' = "none"
    /\ session_view_valid' = FALSE
    /\ zombie_age_stale' = TRUE    \* On retry, the zombie is now older
    /\ step_8_out' = "retry_reset"
    /\ UNCHANGED << session_persisted, updated_at_is_null, zombie_session_exists,
                    current_user, session_owner, zombie_superseded,
                    schema_accepts_null_updated_at,
                    step_1_out, step_2_out, step_3_out, step_4_out, step_5_out, step_6_out, step_7_out >>

\* ====================================================================
\* NEXT STATE RELATION
\* ====================================================================
Next ==
    \* Step 1 (shared)
    \/ Step1_ValidateUrl
    \/ Step1_Error_InvalidRequest
    \/ Step1_Error_Auth
    \* Step 2 (buggy)
    \/ Step2_Buggy_NoActiveSession
    \/ Step2_Buggy_ZombieBlocks
    \* Step 2 (fixed)
    \/ Step2_Fixed_NoActiveForUser
    \/ Step2_Fixed_SupersedeStaleZombie
    \/ Step2_Fixed_OwnFreshSessionBlocks
    \* Step 2 (shared)
    \/ Step2_Error_Persistence
    \* Step 2b (fixed only — finalize stale zombie)
    \/ Step2b_FinalizeStaleZombie
    \/ Step2b_Error_FinalizeFails
    \* Step 3 (buggy vs fixed)
    \/ Step3_Persist_Buggy
    \/ Step3_Persist_Fixed
    \/ Step3_Error_DbInsert
    \* Step 4 (shared)
    \/ Step4_ApiSuccess
    \/ Step4_Error_ResponseValidation
    \* Step 5 (shared)
    \/ Step5_LoadSession
    \* Step 6 (buggy vs fixed)
    \/ Step6_SchemaValid_NonNull
    \/ Step6_Fixed_SchemaAcceptsNull
    \/ Step6_Buggy_SchemaFails
    \* Step 7 (buggy only — retry blocked)
    \/ Step7_Buggy_RetryBlocked
    \* Step 8 (fixed only — retry succeeds)
    \/ Step8_Fixed_RetrySucceeds
    \* Stuttering
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ====================================================================
\* PROPERTIES
\* ====================================================================

\* --- Reachability ---
\* In fixed mode, done is always reachable
ReachabilityDone_Fixed == (mode = "fixed") => <>(pc = "done")

\* In buggy mode, blocked is reachable (confirms the bug)
ReachabilityBlocked_Buggy == (mode = "buggy") => <>(pc = "blocked")

\* In fixed mode, blocked is NEVER reachable
NeverBlocked_Fixed == (mode = "fixed") => [](pc /= "blocked")

\* --- Invariant properties (hold in fixed mode) ---
\* INV-1: PersistedSessionLoadable
\* INV-2: UpdatedAtNonNull
\* INV-3: UserScopedUniqueness
\* INV-4: ZombieRecoverable
\* INV-5: WriteReadConsistency

====
