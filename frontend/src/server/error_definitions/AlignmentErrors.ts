/**
 * AlignmentErrors - Standardized error definitions for client-side alignment validation.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 314-prevent-confirmation-of-misaligned-story-selection
 *
 * Defines user-facing messages for alignment validation failures,
 * including misalignment, unavailable rules, and missing selection.
 */

export const AlignmentErrors = {
  STORY_MISALIGNED: "The selected story does not meet alignment criteria.",
  ALIGNMENT_RULES_UNAVAILABLE: "Alignment validation is temporarily unavailable.",
  GENERIC_SELECTION_REQUIRED: "Please select exactly one story before confirming.",
} as const;

export type AlignmentErrorKey = keyof typeof AlignmentErrors;
