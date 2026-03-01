/**
 * singleStorySelectionVerifier - Validates that exactly one story is selected
 * before allowing confirmation to proceed.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * Pure validation function: checks the count of selected story IDs.
 * Returns a reason code that maps to StorySelectionErrors for display.
 */

import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type ValidationResult =
  | { valid: true }
  | { valid: false; reason?: string };

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/**
 * Validate that exactly one story is selected.
 *
 * @param selected - Array of selected story IDs
 * @returns ValidationResult with reason code on failure
 */
export function validateSingleStorySelection(
  selected: string[],
): ValidationResult {
  if (!Array.isArray(selected)) {
    frontendLogger.error(
      'Verifier misconfiguration',
      new Error('Expected string[] but received non-array'),
      { module: 'singleStorySelectionVerifier', action: 'validate' },
    );
    return { valid: false };
  }

  return selected.length === 1
    ? { valid: true }
    : { valid: false, reason: 'StorySelectionRequired' };
}
