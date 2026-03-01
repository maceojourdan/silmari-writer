/**
 * StorySelectionErrors - Standardized error definitions for story selection validation.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * Defines user-facing messages for story selection validation failures,
 * used by the StorySelectionConfirm component to display feedback when
 * the user attempts to confirm without exactly one story selected.
 */

export const StorySelectionErrors = {
  StorySelectionRequired: {
    code: 'StorySelectionRequired',
    message: 'Please select exactly one story before confirming.',
  },
} as const;

export type StorySelectionErrorKey = keyof typeof StorySelectionErrors;
