/**
 * CaseStateVerifier - Validates allowed state transitions
 * for the case drafting process.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import type { DraftingStatus } from '@/server/data_structures/Case';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface VerificationSuccess {
  valid: true;
}

export interface VerificationFailure {
  valid: false;
  reason: string;
}

export type VerificationResult = VerificationSuccess | VerificationFailure;

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

export const CaseStateVerifier = {
  /**
   * Assert that blocking drafting is allowed from the current state.
   *
   * Drafting can be blocked when:
   * - Current status is 'drafting_allowed'
   *
   * Drafting cannot be re-blocked when:
   * - Current status is already 'blocked_due_to_unverified_claims'
   *
   * @param currentStatus - The current drafting status of the case
   * @returns VerificationResult indicating if the transition is allowed
   */
  assertDraftingBlockAllowed(currentStatus: string): VerificationResult {
    if (currentStatus === 'blocked_due_to_unverified_claims') {
      return {
        valid: false,
        reason: 'Drafting is already blocked due to unverified claims',
      };
    }

    if (currentStatus === 'drafting_allowed') {
      return { valid: true };
    }

    return {
      valid: false,
      reason: `Unknown drafting status: ${currentStatus}`,
    };
  },
} as const;
