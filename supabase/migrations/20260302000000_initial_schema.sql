-- Silmari Writer: Initial Schema Migration
-- 32 tables in FK dependency order + confirm_story RPC + indexes
-- Idempotent: all CREATE TABLE use IF NOT EXISTS

-- ============================================================
-- TIER 1: No FK dependencies
-- ============================================================

CREATE TABLE IF NOT EXISTS users (
  id            uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  sms_opt_in    boolean     NOT NULL DEFAULT false,
  phone_number  text,
  created_at    timestamptz NOT NULL DEFAULT now(),
  updated_at    timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS resumes (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  content     text        NOT NULL,
  name        text        NOT NULL,
  word_count  integer     NOT NULL CHECK (word_count >= 0),
  created_at  timestamptz DEFAULT now()
);

CREATE TABLE IF NOT EXISTS jobs (
  id            uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  title         text        NOT NULL,
  description   text        NOT NULL,
  source_type   text        NOT NULL CHECK (source_type IN ('link','text')),
  source_value  text        NOT NULL,
  created_at    timestamptz DEFAULT now()
);

CREATE TABLE IF NOT EXISTS questions (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  text        text        NOT NULL,
  category    text,
  created_at  timestamptz DEFAULT now()
);

-- ============================================================
-- TIER 2: Depend on Tier 1
-- ============================================================

CREATE TABLE IF NOT EXISTS sessions (
  id                        uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  resume                    jsonb       NOT NULL,
  job                       jsonb       NOT NULL,
  question                  jsonb       NOT NULL,
  state                     text        NOT NULL CHECK (state IN ('initialized','DRAFT','DRAFT_ENABLED','ACTIVE','FINALIZE')),
  required_inputs_complete  boolean,
  responses                 text[],
  created_at                timestamptz NOT NULL DEFAULT now(),
  updated_at                timestamptz
);

CREATE TABLE IF NOT EXISTS job_requirements (
  id            text        PRIMARY KEY,
  description   text        NOT NULL,
  priority      text        CHECK (priority IN ('REQUIRED','PREFERRED','NICE_TO_HAVE')),
  question_id   text        NOT NULL REFERENCES questions(id)
);

CREATE TABLE IF NOT EXISTS claimants (
  id          text        PRIMARY KEY,
  key_claims  jsonb       NOT NULL DEFAULT '[]',
  phone       text,
  sms_opt_in  boolean     NOT NULL DEFAULT false
);

CREATE TABLE IF NOT EXISTS answer_sessions (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id     text        NOT NULL,
  state       text        NOT NULL CHECK (state IN ('INIT','IN_PROGRESS','RECALL','COMPLETE','VERIFY')),
  created_at  timestamptz NOT NULL DEFAULT now(),
  updated_at  timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS cases (
  id                text        PRIMARY KEY,
  claimant_id       text        NOT NULL REFERENCES claimants(id),
  session_id        text        NOT NULL,
  drafting_status   text        NOT NULL CHECK (drafting_status IN ('drafting_allowed','blocked_due_to_unverified_claims')),
  created_at        timestamptz NOT NULL DEFAULT now(),
  updated_at        timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS stories (
  id            text        PRIMARY KEY,
  title         text        NOT NULL,
  summary       text        NOT NULL,
  status        text        NOT NULL DEFAULT 'AVAILABLE' CHECK (status IN ('AVAILABLE','CONFIRMED','EXCLUDED')),
  question_id   text        NOT NULL REFERENCES questions(id)
);

CREATE TABLE IF NOT EXISTS onboarding (
  id            uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id       text        NOT NULL,
  step          integer     NOT NULL CHECK (step >= 1),
  status        text        NOT NULL DEFAULT 'NOT_STARTED' CHECK (status IN ('NOT_STARTED','IN_PROGRESS','COMPLETED')),
  completed_at  timestamptz,
  created_at    timestamptz NOT NULL DEFAULT now(),
  updated_at    timestamptz NOT NULL DEFAULT now()
);

-- ============================================================
-- TIER 3: Depend on Tier 2
-- ============================================================

CREATE TABLE IF NOT EXISTS analytics_events (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  kpi_id      text        NOT NULL,
  user_id     text        NOT NULL,
  timestamp   timestamptz NOT NULL,
  metadata    jsonb       NOT NULL DEFAULT '{}',
  created_at  timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS primary_kpi_events (
  id            uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id       text        NOT NULL,
  action_type   text        NOT NULL,
  metadata      jsonb       NOT NULL DEFAULT '{}',
  status        text        NOT NULL DEFAULT 'PENDING' CHECK (status IN ('PENDING','PERSISTED','ANALYTICS_SENT','ANALYTICS_FAILED')),
  timestamp     timestamptz NOT NULL,
  created_at    timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS events (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  session_id  uuid        NOT NULL REFERENCES sessions(id),
  category    text        NOT NULL CHECK (category IN ('DRAFT','VERIFY','FINALIZE','EDIT','REVISION','SIGNAL')),
  timestamp   timestamptz NOT NULL,
  metadata    jsonb
);

CREATE TABLE IF NOT EXISTS session_metrics (
  id                    uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  session_id            uuid        NOT NULL REFERENCES sessions(id),
  time_to_first_draft   float8      NOT NULL,
  completion_rate       float8      NOT NULL,
  confirmation_rate     float8      NOT NULL,
  signal_density        float8      NOT NULL,
  drop_off              float8      NOT NULL,
  created_at            timestamptz DEFAULT now(),
  updated_at            timestamptz DEFAULT now()
);

CREATE TABLE IF NOT EXISTS session_slots (
  id                uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  session_id        uuid        NOT NULL REFERENCES answer_sessions(id),
  question_type_id  text        NOT NULL,
  slots             jsonb       NOT NULL,
  status            text        NOT NULL CHECK (status IN ('COMPLETE')),
  created_at        timestamptz DEFAULT now(),
  updated_at        timestamptz DEFAULT now()
);

CREATE TABLE IF NOT EXISTS orient_story_records (
  id                uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  story_title       text        NOT NULL,
  initial_context   jsonb       NOT NULL,
  created_at        timestamptz DEFAULT now(),
  updated_at        timestamptz
);

CREATE TABLE IF NOT EXISTS behavioral_questions (
  id            uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  session_id    text        NOT NULL,
  objective     text        NOT NULL,
  actions       jsonb       NOT NULL,
  obstacles     jsonb       NOT NULL,
  outcome       text        NOT NULL,
  role_clarity  text        NOT NULL,
  status        text        NOT NULL DEFAULT 'DRAFT' CHECK (status IN ('DRAFT','VERIFY')),
  created_at    timestamptz DEFAULT now(),
  updated_at    timestamptz DEFAULT now()
);

CREATE TABLE IF NOT EXISTS content (
  id              uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  body            text,
  status          text        NOT NULL CHECK (status IN ('DRAFT','REVIEW','APPROVED','FINALIZE')),
  workflow_stage  text        NOT NULL CHECK (workflow_stage IN ('DRAFTING','REVIEW','FINALIZE','COMPLETE')),
  created_at      timestamptz NOT NULL DEFAULT now(),
  updated_at      timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS answers (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  status      text        NOT NULL CHECK (status IN ('DRAFT','COMPLETED','FINALIZED')),
  finalized   boolean     NOT NULL DEFAULT false,
  editable    boolean     NOT NULL DEFAULT true,
  locked      boolean     NOT NULL DEFAULT false,
  content     text        NOT NULL,
  user_id     text        NOT NULL,
  created_at  timestamptz NOT NULL DEFAULT now(),
  updated_at  timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS drafts (
  id                uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  status            text        NOT NULL CHECK (status IN ('DRAFT','APPROVED','FINALIZED')),
  content           text        NOT NULL,
  title             text,
  user_id           text        NOT NULL,
  resume_id         uuid        REFERENCES resumes(id),
  job_id            uuid        REFERENCES jobs(id),
  question_id       uuid        REFERENCES questions(id),
  voice_session_id  uuid        REFERENCES answer_sessions(id),
  claim_set_id      uuid,
  sections          jsonb,
  interaction_data  jsonb,
  approved_at       timestamptz,
  finalized_at      timestamptz,
  created_at        timestamptz NOT NULL DEFAULT now(),
  updated_at        timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS story_records (
  id                uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  session_id        uuid        REFERENCES sessions(id),
  draft_id          uuid        REFERENCES drafts(id),
  resume_id         uuid        REFERENCES resumes(id),
  job_id            uuid        REFERENCES jobs(id),
  question_id       uuid        REFERENCES questions(id),
  voice_session_id  uuid        REFERENCES answer_sessions(id),
  user_id           text        NOT NULL,
  status            text        NOT NULL CHECK (status IN ('DRAFT','APPROVED','FINALIZED','INIT','IN_PROGRESS','RECALL','COMPLETE','VERIFY')),
  content           text,
  draft_text        text,
  claims_used       text[],
  truth_checks      jsonb,
  responses         text[],
  created_at        timestamptz DEFAULT now(),
  updated_at        timestamptz DEFAULT now()
);

-- ============================================================
-- TIER 4: Depend on Tier 3
-- ============================================================

CREATE TABLE IF NOT EXISTS claims (
  id              text        PRIMARY KEY,
  content         text        NOT NULL,
  status          text        NOT NULL CHECK (status IN ('UNCERTAIN','CONFIRMED','DENIED','PENDING','UNVERIFIED','unverified','verified','not_verified','confirmed','unconfirmed','rejected')),
  sms_opt_in      boolean     NOT NULL DEFAULT false,
  phone_number    text,
  truth_checks    jsonb       NOT NULL DEFAULT '[]',
  session_id      text,
  case_id         text        REFERENCES cases(id),
  story_record_id text,
  claim_set_id    uuid,
  category        text        CHECK (category IN ('metrics','scope','production','security')),
  contact_phone   text,
  contact_method  text        CHECK (contact_method IN ('sms','voice')),
  metric          text,
  scope           text,
  context         text,
  section         text        CHECK (section IN ('context','actions','outcome')),
  "order"         integer,
  verified_at     timestamptz,
  disputed_at     timestamptz,
  created_at      timestamptz NOT NULL DEFAULT now(),
  updated_at      timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS sms_follow_ups (
  id            uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  answer_id     uuid        NOT NULL REFERENCES answers(id),
  phone_number  text        NOT NULL,
  message       text        NOT NULL,
  status        text        NOT NULL CHECK (status IN ('sent','failed')),
  message_id    text,
  created_at    timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS verification_requests (
  id              text        PRIMARY KEY,
  session_id      text        NOT NULL,
  status          text        NOT NULL CHECK (status IN ('pending','confirmed','failed','timed_out')),
  attempt_count   integer     NOT NULL DEFAULT 0,
  token           text        NOT NULL UNIQUE,
  claim_ids       jsonb       NOT NULL DEFAULT '[]',
  contact_phone   text        NOT NULL,
  contact_method  text        NOT NULL CHECK (contact_method IN ('sms','voice')),
  responded_at    timestamptz,
  created_at      timestamptz NOT NULL DEFAULT now(),
  updated_at      timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS truth_checks (
  id          text        PRIMARY KEY,
  claim_id    text        NOT NULL REFERENCES claims(id),
  status      text        NOT NULL CHECK (status IN ('confirmed','denied')),
  source      text        NOT NULL,
  created_at  timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS drafting_workflows (
  id          text        PRIMARY KEY,
  claim_id    text        NOT NULL REFERENCES claims(id),
  status      text        NOT NULL CHECK (status IN ('Ready','On Hold','In Progress','Completed')),
  reason      text,
  created_at  timestamptz NOT NULL DEFAULT now(),
  updated_at  timestamptz NOT NULL DEFAULT now()
);

-- ============================================================
-- TIER 5: Depend on Tier 4
-- ============================================================

CREATE TABLE IF NOT EXISTS delivery_attempts (
  id              text        PRIMARY KEY,
  request_id      text        NOT NULL REFERENCES verification_requests(id),
  attempt_number  integer     NOT NULL CHECK (attempt_number >= 1),
  status          text        NOT NULL CHECK (status IN ('success','failed')),
  external_id     text,
  error_message   text,
  created_at      timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS verification_attempts (
  id                text        PRIMARY KEY,
  claimant_id       text        NOT NULL REFERENCES claimants(id),
  status            text        NOT NULL CHECK (status IN ('FAILED','PENDING','PASSED')),
  reason            text,
  drafting_status   text        CHECK (drafting_status IN ('ALLOWED','BLOCKED','IN_PROGRESS')),
  created_at        timestamptz NOT NULL DEFAULT now(),
  updated_at        timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS draft_metrics (
  id                  uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  draft_id            uuid        NOT NULL REFERENCES drafts(id),
  time_to_draft       float8      NOT NULL,
  confirmation_rate   float8      NOT NULL,
  signal_density      float8      NOT NULL,
  created_at          timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS draft_versions (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  draft_id    uuid        NOT NULL REFERENCES drafts(id),
  version     integer     NOT NULL DEFAULT 1,
  content     text        NOT NULL,
  created_at  timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS story_metrics (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  session_id  uuid        NOT NULL REFERENCES sessions(id),
  story_id    uuid,
  metric_type text        NOT NULL,
  value       float8      NOT NULL,
  created_at  timestamptz NOT NULL DEFAULT now()
);

-- ============================================================
-- CONFIRM_STORY RPC FUNCTION
-- ============================================================

CREATE OR REPLACE FUNCTION confirm_story(
  p_story_id    text,
  p_claim_ids   text[],
  p_new_status  text DEFAULT 'CONFIRMED'
)
RETURNS jsonb
LANGUAGE plpgsql
AS $$
DECLARE
  v_result jsonb;
BEGIN
  -- Update story status
  UPDATE stories
  SET status = p_new_status
  WHERE id = p_story_id;

  -- Update claims status to confirmed
  UPDATE claims
  SET status = 'CONFIRMED',
      updated_at = now()
  WHERE id = ANY(p_claim_ids);

  v_result := jsonb_build_object(
    'story_id', p_story_id,
    'claims_updated', array_length(p_claim_ids, 1),
    'new_status', p_new_status
  );

  RETURN v_result;
END;
$$;

-- ============================================================
-- INDEXES on FK columns
-- ============================================================

CREATE INDEX IF NOT EXISTS idx_sessions_state ON sessions(state);
CREATE INDEX IF NOT EXISTS idx_answer_sessions_user_id ON answer_sessions(user_id);
CREATE INDEX IF NOT EXISTS idx_story_records_session_id ON story_records(session_id);
CREATE INDEX IF NOT EXISTS idx_story_records_draft_id ON story_records(draft_id);
CREATE INDEX IF NOT EXISTS idx_story_records_resume_id ON story_records(resume_id);
CREATE INDEX IF NOT EXISTS idx_story_records_job_id ON story_records(job_id);
CREATE INDEX IF NOT EXISTS idx_story_records_question_id ON story_records(question_id);
CREATE INDEX IF NOT EXISTS idx_story_records_voice_session_id ON story_records(voice_session_id);
CREATE INDEX IF NOT EXISTS idx_drafts_resume_id ON drafts(resume_id);
CREATE INDEX IF NOT EXISTS idx_drafts_job_id ON drafts(job_id);
CREATE INDEX IF NOT EXISTS idx_drafts_question_id ON drafts(question_id);
CREATE INDEX IF NOT EXISTS idx_drafts_voice_session_id ON drafts(voice_session_id);
CREATE INDEX IF NOT EXISTS idx_claims_session_id ON claims(session_id);
CREATE INDEX IF NOT EXISTS idx_claims_case_id ON claims(case_id);
CREATE INDEX IF NOT EXISTS idx_claims_story_record_id ON claims(story_record_id);
CREATE INDEX IF NOT EXISTS idx_claims_claim_set_id ON claims(claim_set_id);
CREATE INDEX IF NOT EXISTS idx_truth_checks_claim_id ON truth_checks(claim_id);
CREATE INDEX IF NOT EXISTS idx_drafting_workflows_claim_id ON drafting_workflows(claim_id);
CREATE INDEX IF NOT EXISTS idx_verification_requests_session_id ON verification_requests(session_id);
CREATE INDEX IF NOT EXISTS idx_verification_requests_token ON verification_requests(token);
CREATE INDEX IF NOT EXISTS idx_delivery_attempts_request_id ON delivery_attempts(request_id);
CREATE INDEX IF NOT EXISTS idx_verification_attempts_claimant_id ON verification_attempts(claimant_id);
CREATE INDEX IF NOT EXISTS idx_draft_metrics_draft_id ON draft_metrics(draft_id);
CREATE INDEX IF NOT EXISTS idx_draft_versions_draft_id ON draft_versions(draft_id);
CREATE INDEX IF NOT EXISTS idx_story_metrics_session_id ON story_metrics(session_id);
CREATE INDEX IF NOT EXISTS idx_events_session_id ON events(session_id);
CREATE INDEX IF NOT EXISTS idx_session_metrics_session_id ON session_metrics(session_id);
CREATE INDEX IF NOT EXISTS idx_session_slots_session_id ON session_slots(session_id);
CREATE INDEX IF NOT EXISTS idx_sms_follow_ups_answer_id ON sms_follow_ups(answer_id);
CREATE INDEX IF NOT EXISTS idx_cases_claimant_id ON cases(claimant_id);
CREATE INDEX IF NOT EXISTS idx_stories_question_id ON stories(question_id);
CREATE INDEX IF NOT EXISTS idx_job_requirements_question_id ON job_requirements(question_id);
CREATE INDEX IF NOT EXISTS idx_onboarding_user_id ON onboarding(user_id);
CREATE INDEX IF NOT EXISTS idx_analytics_events_user_id ON analytics_events(user_id);
CREATE INDEX IF NOT EXISTS idx_primary_kpi_events_user_id ON primary_kpi_events(user_id);
