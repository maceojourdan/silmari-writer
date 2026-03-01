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
  StoryConfirmStatus,
} from '@/server/data_structures/ConfirmStory';

export const ConfirmStoryDAO = {
  /**
   * Fetch the active question by ID.
   */
  async findQuestionById(questionId: string): Promise<Question | null> {
    // Supabase: supabase.from('questions').select('*').eq('id', questionId).single()
    throw new Error('ConfirmStoryDAO.findQuestionById not yet wired to Supabase');
  },

  /**
   * Fetch job requirements associated with a question.
   */
  async findJobRequirementsByQuestionId(questionId: string): Promise<JobRequirement[]> {
    // Supabase: supabase.from('job_requirements').select('*').eq('question_id', questionId)
    throw new Error('ConfirmStoryDAO.findJobRequirementsByQuestionId not yet wired to Supabase');
  },

  /**
   * Fetch all available stories for a given question.
   */
  async findStoriesByQuestionId(questionId: string): Promise<Story[]> {
    // Supabase: supabase.from('stories').select('*').eq('question_id', questionId)
    throw new Error('ConfirmStoryDAO.findStoriesByQuestionId not yet wired to Supabase');
  },

  /**
   * Find a specific story by ID.
   */
  async findStoryById(storyId: string): Promise<Story | null> {
    // Supabase: supabase.from('stories').select('*').eq('id', storyId).single()
    throw new Error('ConfirmStoryDAO.findStoryById not yet wired to Supabase');
  },

  /**
   * Transactionally update story statuses:
   * - Set the confirmed story to CONFIRMED
   * - Set all other stories for the question to EXCLUDED
   *
   * Uses a Supabase RPC or SQL transaction to ensure atomicity.
   * Returns the count of excluded stories.
   */
  async updateStatusesTransactional(
    questionId: string,
    confirmedStoryId: string,
  ): Promise<{ confirmedStoryId: string; excludedCount: number }> {
    // Supabase RPC: supabase.rpc('confirm_story', { p_question_id: questionId, p_story_id: confirmedStoryId })
    throw new Error('ConfirmStoryDAO.updateStatusesTransactional not yet wired to Supabase');
  },
} as const;
