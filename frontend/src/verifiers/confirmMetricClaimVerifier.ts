/**
 * confirmMetricClaimVerifier - Client-side validation enforcing
 * that a confirmation decision (Y/N) has been selected before submission.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Enforces:
 * - decision must be "Y" or "N" (not undefined, null, or empty)
 */

export interface DecisionValidationResult {
  isValid: boolean;
  error?: string;
}

/**
 * Validate that a confirmation decision has been made.
 * Returns isValid true if decision is "Y" or "N", otherwise false with error.
 */
export function validateDecision(
  decision?: 'Y' | 'N',
): DecisionValidationResult {
  if (!decision || (decision !== 'Y' && decision !== 'N')) {
    return {
      isValid: false,
      error: 'Please make a selection before submitting',
    };
  }

  return { isValid: true };
}
