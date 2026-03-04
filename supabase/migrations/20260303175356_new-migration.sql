ALTER TABLE story_records
ADD COLUMN IF NOT EXISTS question_progress jsonb;
