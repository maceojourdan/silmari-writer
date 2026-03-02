/**
 * ConfirmStoryDAO - Data access object for the confirm-aligned-story-selection path.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 313-confirm-aligned-story-selection
 *
 * In production, performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type {
  Question,
  JobRequirement,
  Story,
} from '@/server/data_structures/ConfirmStory';
import { supabase } from '@/lib/supabase';
import { ConfirmStoryErrors, ConfirmStoryError } from '@/server/error_definitions/ConfirmStoryErrors';

export const ConfirmStoryDAO = {
  async findQuestionById(questionId: string): Promise<Question | null> {
    try {
      const { data, error } = await supabase
        .from('questions')
        .select('*')
        .eq('id', questionId)
        .maybeSingle();

      if (error) throw ConfirmStoryErrors.DataNotFound(`Failed to find question: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        text: data.text,
        category: data.category,
      };
    } catch (err) {
      if (err instanceof ConfirmStoryError) throw err;
      throw ConfirmStoryErrors.DataNotFound(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findJobRequirementsByQuestionId(questionId: string): Promise<JobRequirement[]> {
    try {
      const { data, error } = await supabase
        .from('job_requirements')
        .select('*')
        .eq('question_id', questionId);

      if (error) throw ConfirmStoryErrors.DataNotFound(`Failed to find job requirements: ${error.message}`);

      return (data ?? []).map((row: Record<string, unknown>) => ({
        id: row.id as string,
        description: row.description as string,
        priority: row.priority as string | undefined,
      })) as JobRequirement[];
    } catch (err) {
      if (err instanceof ConfirmStoryError) throw err;
      throw ConfirmStoryErrors.DataNotFound(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findStoriesByQuestionId(questionId: string): Promise<Story[]> {
    try {
      const { data, error } = await supabase
        .from('stories')
        .select('*')
        .eq('question_id', questionId);

      if (error) throw ConfirmStoryErrors.DataNotFound(`Failed to find stories: ${error.message}`);

      return (data ?? []).map((row: Record<string, unknown>) => ({
        id: row.id as string,
        title: row.title as string,
        summary: row.summary as string,
        status: row.status as string,
        questionId: row.question_id as string,
      })) as Story[];
    } catch (err) {
      if (err instanceof ConfirmStoryError) throw err;
      throw ConfirmStoryErrors.DataNotFound(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findStoryById(storyId: string): Promise<Story | null> {
    try {
      const { data, error } = await supabase
        .from('stories')
        .select('*')
        .eq('id', storyId)
        .maybeSingle();

      if (error) throw ConfirmStoryErrors.StoryNotFound(`Failed to find story: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        title: data.title,
        summary: data.summary,
        status: data.status,
        questionId: data.question_id,
      };
    } catch (err) {
      if (err instanceof ConfirmStoryError) throw err;
      throw ConfirmStoryErrors.StoryNotFound(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatusesTransactional(
    questionId: string,
    confirmedStoryId: string,
  ): Promise<{ confirmedStoryId: string; excludedCount: number }> {
    try {
      const { data, error } = await supabase.rpc('confirm_story', {
        p_question_id: questionId,
        p_story_id: confirmedStoryId,
      });

      if (error) throw ConfirmStoryErrors.ConfirmationFailed(`RPC failed: ${error.message}`);
      if (!data) throw ConfirmStoryErrors.ConfirmationFailed('No data returned from RPC');

      return {
        confirmedStoryId: data.confirmed_story_id,
        excludedCount: data.excluded_count,
      };
    } catch (err) {
      if (err instanceof ConfirmStoryError) throw err;
      throw ConfirmStoryErrors.ConfirmationFailed(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
