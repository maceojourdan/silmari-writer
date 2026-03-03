-- Channel ingestion + acceleration persistence foundations
-- Paths: 340-345 follow-on data model contracts

-- ------------------------------------------------------------
-- users extensions for channel sender resolution
-- ------------------------------------------------------------

ALTER TABLE users
  ADD COLUMN IF NOT EXISTS email text;

CREATE UNIQUE INDEX IF NOT EXISTS idx_users_email_unique
  ON users (lower(email))
  WHERE email IS NOT NULL;

CREATE UNIQUE INDEX IF NOT EXISTS idx_users_phone_number_unique
  ON users (phone_number)
  WHERE phone_number IS NOT NULL;

-- ------------------------------------------------------------
-- candidate_profile_baselines
-- ------------------------------------------------------------

CREATE TABLE IF NOT EXISTS candidate_profile_baselines (
  id                   uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id              text        NOT NULL,
  mode                 text        NOT NULL CHECK (mode IN ('url', 'manual', 'oauth', 'skip')),
  linkedin_profile_url text,
  manual_profile       jsonb       NOT NULL DEFAULT '{}',
  resume_snapshot      jsonb       NOT NULL DEFAULT '{}',
  job_focus            jsonb       NOT NULL DEFAULT '{}',
  created_at           timestamptz NOT NULL DEFAULT now(),
  updated_at           timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_candidate_profile_baselines_user_id_unique
  ON candidate_profile_baselines(user_id);

-- ------------------------------------------------------------
-- linkedin_connections (server-side token envelope)
-- ------------------------------------------------------------

CREATE TABLE IF NOT EXISTS linkedin_connections (
  id                        uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id                   text        NOT NULL,
  access_token_ciphertext   text,
  refresh_token_ciphertext  text,
  key_id                    text,
  token_scope               text[]      NOT NULL DEFAULT '{}',
  expires_at                timestamptz,
  refresh_expires_at        timestamptz,
  revoked_at                timestamptz,
  created_at                timestamptz NOT NULL DEFAULT now(),
  updated_at                timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_linkedin_connections_user_id_unique
  ON linkedin_connections(user_id);

-- ------------------------------------------------------------
-- shortlist entities
-- ------------------------------------------------------------

CREATE TABLE IF NOT EXISTS company_shortlists (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id     text        NOT NULL,
  name        text        NOT NULL DEFAULT 'default',
  source      text        NOT NULL CHECK (source IN ('ai', 'manual', 'mixed')),
  created_at  timestamptz NOT NULL DEFAULT now(),
  updated_at  timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_company_shortlists_user_name_unique
  ON company_shortlists(user_id, name);

CREATE TABLE IF NOT EXISTS shortlist_items (
  id            uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  shortlist_id  uuid        NOT NULL REFERENCES company_shortlists(id) ON DELETE CASCADE,
  company_id    text        NOT NULL,
  company_name  text        NOT NULL,
  rank          integer     NOT NULL DEFAULT 0 CHECK (rank >= 0),
  status        text        NOT NULL DEFAULT 'suggested' CHECK (status IN ('suggested', 'saved', 'dismissed')),
  created_at    timestamptz NOT NULL DEFAULT now(),
  updated_at    timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_shortlist_items_shortlist_company_unique
  ON shortlist_items(shortlist_id, company_id);

-- ------------------------------------------------------------
-- contribution + contact + drafts
-- ------------------------------------------------------------

CREATE TABLE IF NOT EXISTS company_contribution_areas (
  id          uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id     text        NOT NULL,
  company_id  text        NOT NULL,
  label       text        NOT NULL,
  rationale   text,
  created_at  timestamptz NOT NULL DEFAULT now(),
  updated_at  timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_company_contribution_areas_unique
  ON company_contribution_areas(user_id, company_id, label);

CREATE TABLE IF NOT EXISTS company_contact_suggestions (
  id                   uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id              text        NOT NULL,
  company_id           text        NOT NULL,
  contact_external_id  text        NOT NULL,
  full_name            text,
  title                text,
  profile_url          text,
  confidence           float8,
  metadata             jsonb       NOT NULL DEFAULT '{}',
  created_at           timestamptz NOT NULL DEFAULT now(),
  updated_at           timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_company_contact_suggestions_unique
  ON company_contact_suggestions(user_id, company_id, contact_external_id);

CREATE TABLE IF NOT EXISTS outreach_drafts (
  id                   uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id              text        NOT NULL,
  company_id           text        NOT NULL,
  contact_external_id  text,
  draft_hash           text        NOT NULL,
  content              text        NOT NULL,
  metadata             jsonb       NOT NULL DEFAULT '{}',
  created_at           timestamptz NOT NULL DEFAULT now(),
  updated_at           timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_outreach_drafts_user_hash_unique
  ON outreach_drafts(user_id, draft_hash);

CREATE TABLE IF NOT EXISTS linkedin_post_drafts (
  id                   uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id              text        NOT NULL,
  company_id           text        NOT NULL,
  contribution_label   text,
  draft_hash           text        NOT NULL,
  content              text        NOT NULL,
  metadata             jsonb       NOT NULL DEFAULT '{}',
  created_at           timestamptz NOT NULL DEFAULT now(),
  updated_at           timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_linkedin_post_drafts_user_hash_unique
  ON linkedin_post_drafts(user_id, draft_hash);

-- ------------------------------------------------------------
-- ingestion_messages (idempotency + channel reply status)
-- ------------------------------------------------------------

CREATE TABLE IF NOT EXISTS ingestion_messages (
  id                   uuid        PRIMARY KEY DEFAULT gen_random_uuid(),
  provider_name        text        NOT NULL,
  provider_message_id  text        NOT NULL,
  channel              text        NOT NULL CHECK (channel IN ('email', 'sms')),
  sender               text        NOT NULL,
  user_id              text        NOT NULL,
  raw_body             text        NOT NULL,
  canonical_url        text        NOT NULL,
  source_domain        text        NOT NULL,
  status               text        NOT NULL CHECK (status IN ('received', 'context_ready', 'context_failed')),
  reply_status         text        NOT NULL DEFAULT 'pending' CHECK (reply_status IN ('pending', 'sent', 'failed_non_blocking')),
  reply_error_code     text,
  session_id           uuid        REFERENCES sessions(id),
  received_at          timestamptz NOT NULL,
  created_at           timestamptz NOT NULL DEFAULT now(),
  updated_at           timestamptz NOT NULL DEFAULT now()
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_ingestion_messages_provider_message_unique
  ON ingestion_messages(provider_name, provider_message_id);

CREATE UNIQUE INDEX IF NOT EXISTS idx_ingestion_messages_user_canonical_url_unique
  ON ingestion_messages(user_id, canonical_url);

CREATE INDEX IF NOT EXISTS idx_ingestion_messages_session_id
  ON ingestion_messages(session_id);

CREATE INDEX IF NOT EXISTS idx_ingestion_messages_status
  ON ingestion_messages(status);

