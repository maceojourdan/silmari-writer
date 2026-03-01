/**
 * StoryAlignmentVerifier - Validates that a selected story is eligible for
 * confirmation against the active question and job requirements.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 313-confirm-aligned-story-selection
 *
 * Checks:
 * 1. Story exists in the available stories list
 * 2. Story is not already confirmed
 * 3. Story is aligned with the question (matching questionId, status AVAILABLE)
 */

import type { Question, Story, JobRequirement, ValidationResult } from '@/server/data_structures/ConfirmStory';

export const StoryAlignmentVerifier = {
  /**
   * Validate that the selected story is eligible for confirmation.
   *
   * @param question - The active question
   * @param story - The story to validate
   * @param requirements - The job requirements for context
   * @param availableStories - All stories for this question
   * @returns ValidationResult - { valid: true } or { valid: false, errors: [...] }
   */
  validate(
    question: Question,
    story: Story,
    requirements: JobRequirement[],
    availableStories: Story[],
  ): ValidationResult {
    const errors: string[] = [];

    // Check 1: Story exists in available stories list
    const storyExists = availableStories.some((s) => s.id === story.id);
    if (!storyExists) {
      errors.push('STORY_NOT_FOUND');
      return { valid: false, errors };
    }

    // Check 2: Story is not already confirmed
    if (story.status === 'CONFIRMED') {
      errors.push('STORY_ALREADY_CONFIRMED');
      return { valid: false, errors };
    }

    // Check 3: Story is aligned with the question
    if (story.questionId !== question.id) {
      errors.push('STORY_NOT_ALIGNED');
      return { valid: false, errors };
    }

    // Check 4: Story must be in AVAILABLE status (not EXCLUDED)
    if (story.status !== 'AVAILABLE') {
      errors.push('STORY_NOT_ALIGNED');
      return { valid: false, errors };
    }

    return { valid: true };
  },
} as const;
