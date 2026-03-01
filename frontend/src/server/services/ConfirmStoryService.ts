/**
 * ConfirmStoryService - Coordinates validation and persistence for story confirmation.
 *
 * Orchestrates the StoryAlignmentVerifier and ConfirmStoryDAO to:
 * 1. Validate the story is eligible for confirmation
 * 2. Transactionally mark the selected story as CONFIRMED
 * 3. Mark all other stories for the question as EXCLUDED
 *
 * Resource: db-h2s4 (service)
 * Path: 313-confirm-aligned-story-selection
 */

import { ConfirmStoryDAO } from '@/server/data_access_objects/ConfirmStoryDAO';
import { StoryAlignmentVerifier } from '@/server/verifiers/StoryAlignmentVerifier';
import { ConfirmStoryError, ConfirmStoryErrors } from '@/server/error_definitions/ConfirmStoryErrors';
import type { ConfirmStoryRequest, ConfirmStoryResponse } from '@/server/data_structures/ConfirmStory';

export const ConfirmStoryService = {
  /**
   * Confirm a selected story for a question.
   *
   * Steps:
   * 1. Fetch question and validate existence
   * 2. Fetch job requirements
   * 3. Fetch all stories for the question
   * 4. Find the selected story
   * 5. Validate alignment with StoryAlignmentVerifier
   * 6. Transactionally update statuses via DAO
   * 7. Return confirmation response
   *
   * @throws ConfirmStoryError on any failure
   */
  async confirm(request: ConfirmStoryRequest): Promise<ConfirmStoryResponse> {
    const { questionId, storyId } = request;

    // Step 1: Fetch and validate question
    const question = await ConfirmStoryDAO.findQuestionById(questionId);
    if (!question) {
      throw ConfirmStoryErrors.DataNotFound(`Question not found: ${questionId}`);
    }

    // Step 2: Fetch job requirements
    const requirements = await ConfirmStoryDAO.findJobRequirementsByQuestionId(questionId);

    // Step 3: Fetch all stories for the question
    const allStories = await ConfirmStoryDAO.findStoriesByQuestionId(questionId);

    // Step 4: Find the selected story
    const story = await ConfirmStoryDAO.findStoryById(storyId);
    if (!story) {
      throw ConfirmStoryErrors.StoryNotFound(`Story not found: ${storyId}`);
    }

    // Step 5: Validate alignment
    const validation = StoryAlignmentVerifier.validate(
      question,
      story,
      requirements,
      allStories,
    );

    if (!validation.valid) {
      const errorCode = validation.errors[0];
      if (errorCode === 'STORY_NOT_FOUND') {
        throw ConfirmStoryErrors.StoryNotFound();
      }
      if (errorCode === 'STORY_ALREADY_CONFIRMED') {
        throw ConfirmStoryErrors.StoryAlreadyConfirmed();
      }
      if (errorCode === 'STORY_NOT_ALIGNED') {
        throw ConfirmStoryErrors.StoryNotAligned();
      }
      throw ConfirmStoryErrors.ConfirmationFailed(
        `Validation failed: ${validation.errors.join(', ')}`,
      );
    }

    // Step 6: Transactionally update statuses
    try {
      const result = await ConfirmStoryDAO.updateStatusesTransactional(
        questionId,
        storyId,
      );

      // Step 7: Build and return response
      const confirmedStory = {
        ...story,
        status: 'CONFIRMED' as const,
      };

      return {
        confirmedStoryId: result.confirmedStoryId,
        status: 'CONFIRMED',
        story: confirmedStory,
        excludedCount: result.excludedCount,
      };
    } catch (error) {
      if (error instanceof ConfirmStoryError) {
        throw error;
      }

      throw ConfirmStoryErrors.PersistenceFailure(
        `Failed to persist story confirmation: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },
} as const;
