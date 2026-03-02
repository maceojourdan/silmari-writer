/**
 * OnboardingCompletionVerifier - Validates client-side onboarding step
 * completion before API submission.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * Validates:
 *   - userId is a non-empty string (after trimming)
 *   - step is a positive integer
 *
 * Returns:
 *   - { valid: true, payload: CompleteOnboardingStepPayload } on success
 *   - { valid: false, errors: string[] } on failure
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type CompleteOnboardingStepPayload = {
  userId: string;
  step: number;
  metadata?: Record<string, unknown>;
};

type ValidationSuccess = {
  valid: true;
  payload: CompleteOnboardingStepPayload;
};
type ValidationFailure = { valid: false; errors: string[] };
export type OnboardingCompletionValidationResult =
  | ValidationSuccess
  | ValidationFailure;

// ---------------------------------------------------------------------------
// Schema
// ---------------------------------------------------------------------------

const OnboardingCompletionSchema = z.object({
  userId: z.string().min(1, 'User ID is required'),
  step: z
    .number()
    .int('Step must be an integer')
    .min(1, 'Step must be at least 1'),
});

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

export function validateOnboardingCompletion(
  userId: string,
  step: number,
  metadata?: Record<string, unknown>,
): OnboardingCompletionValidationResult {
  const trimmedUserId = userId.trim();

  const parsed = OnboardingCompletionSchema.safeParse({
    userId: trimmedUserId,
    step,
  });

  if (!parsed.success) {
    const errors = parsed.error.issues.map((issue) => issue.message);
    return { valid: false, errors };
  }

  return {
    valid: true,
    payload: { userId: trimmedUserId, step, metadata },
  };
}
