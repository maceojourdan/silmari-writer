-- Align confirm_story RPC contract with the app-level confirm story flow.
-- Expected RPC call shape:
--   confirm_story(p_question_id uuid, p_story_id text)
-- Expected JSON payload:
--   { confirmed_story_id: text, excluded_count: integer }

DROP FUNCTION IF EXISTS public.confirm_story(text, text[], text);
DROP FUNCTION IF EXISTS public.confirm_story(text, text[]);

CREATE OR REPLACE FUNCTION public.confirm_story(
  p_question_id uuid,
  p_story_id text
)
RETURNS jsonb
LANGUAGE plpgsql
AS $$
DECLARE
  v_confirmed_story_id text;
  v_excluded_count integer := 0;
BEGIN
  UPDATE public.stories
  SET status = 'CONFIRMED'
  WHERE question_id = p_question_id
    AND id = p_story_id
  RETURNING id INTO v_confirmed_story_id;

  IF v_confirmed_story_id IS NULL THEN
    RAISE EXCEPTION 'Story % not found for question %', p_story_id, p_question_id
      USING ERRCODE = 'P0002';
  END IF;

  UPDATE public.stories
  SET status = 'EXCLUDED'
  WHERE question_id = p_question_id
    AND id <> p_story_id
    AND status IS DISTINCT FROM 'EXCLUDED';

  GET DIAGNOSTICS v_excluded_count = ROW_COUNT;

  RETURN jsonb_build_object(
    'confirmed_story_id', v_confirmed_story_id,
    'excluded_count', v_excluded_count
  );
END;
$$;
