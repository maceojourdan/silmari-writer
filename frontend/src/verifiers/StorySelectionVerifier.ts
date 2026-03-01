/**
 * StorySelectionVerifier - Validates that exactly one story is selected
 * before allowing confirmation submission.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 313-confirm-aligned-story-selection
 */

import type { Story } from '@/server/data_structures/ConfirmStory';

export type VerificationSuccess = { valid: true };
export type VerificationFailure = { valid: false; errors: string[] };
export type VerificationResult = VerificationSuccess | VerificationFailure;

export const StorySelectionVerifier = {
  /**
   * Verify that exactly one story is selected and it exists in the available stories.
   *
   * @param selectedStoryId - The ID of the selected story (null if none selected)
   * @param availableStories - The list of available stories
   * @returns VerificationResult
   */
  verify(
    selectedStoryId: string | null,
    availableStories: Story[],
  ): VerificationResult {
    const errors: string[] = [];

    if (!selectedStoryId) {
      errors.push('Please select a story before confirming');
      return { valid: false, errors };
    }

    const storyExists = availableStories.some((s) => s.id === selectedStoryId);
    if (!storyExists) {
      errors.push('Selected story is not in the available stories list');
      return { valid: false, errors };
    }

    return { valid: true };
  },
} as const;
