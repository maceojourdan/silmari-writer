/**
 * AlignmentVerifier - Client-side alignment validation for story selection.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 314-prevent-confirmation-of-misaligned-story-selection
 *
 * Validates that a selected story is aligned with the active question
 * and job requirements before allowing confirmation to proceed.
 */

import type { Story } from '@/server/data_structures/ConfirmStory';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type ConfirmationPayload = {
  storyId: string;
  questionId: string;
  jobId: string;
};

export type AlignmentRules = {
  activeQuestionId: string;
  stories: Pick<Story, 'id' | 'questionId' | 'status'>[];
} | null;

export type AlignmentResult = {
  status: "aligned" | "misaligned";
  messageKey?: string;
};

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

export const AlignmentVerifier = {
  /**
   * Validate that the selected story is aligned with the active question.
   *
   * Pure function: accepts injected rules to evaluate alignment.
   *
   * @param payload - The confirmation request payload (storyId, questionId, jobId)
   * @param rules   - Alignment rules including active question and story metadata, or null
   * @returns AlignmentResult indicating aligned or misaligned with optional messageKey
   */
  validate(
    payload: ConfirmationPayload,
    rules: AlignmentRules,
  ): AlignmentResult {
    // If rules are unavailable, treat as validation failure
    if (rules === null) {
      return { status: 'misaligned', messageKey: 'ALIGNMENT_RULES_UNAVAILABLE' };
    }

    // Find the selected story in the rules
    const story = rules.stories.find((s) => s.id === payload.storyId);

    // Story not found in available stories
    if (!story) {
      return { status: 'misaligned', messageKey: 'STORY_MISALIGNED' };
    }

    // Story's questionId must match the active question
    if (story.questionId !== rules.activeQuestionId) {
      return { status: 'misaligned', messageKey: 'STORY_MISALIGNED' };
    }

    // Story must be in AVAILABLE status (not EXCLUDED or CONFIRMED)
    if (story.status !== 'AVAILABLE') {
      return { status: 'misaligned', messageKey: 'STORY_MISALIGNED' };
    }

    return { status: 'aligned' };
  },
} as const;
