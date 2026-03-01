/**
 * ContactMethodVerifier - Validates that a claimant has at least one
 * supported contact method (voice or SMS) for verification.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 323-fail-verification-when-no-contact-method
 */

import type { Claimant } from '@/server/data_structures/Claimant';
import { VerificationErrors } from '@/server/error_definitions/VerificationErrors';
import { verificationLogger } from '@/server/logging/verificationLogger';

// ---------------------------------------------------------------------------
// Result type
// ---------------------------------------------------------------------------

export interface ContactMethodResult {
  hasContactMethod: boolean;
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

export const ContactMethodVerifier = {
  /**
   * Check whether the claimant has at least one supported contact method.
   *
   * Voice is available if `profile.phone` is truthy.
   * SMS is available if `profile.phone` is truthy AND `profile.smsOptIn` is true.
   *
   * @param profile - Claimant profile with contact fields
   * @returns { hasContactMethod: boolean }
   * @throws VerificationErrors.INTERNAL_VALIDATION_ERROR for malformed input
   */
  validate(profile: Claimant): ContactMethodResult {
    try {
      if (!profile || typeof profile !== 'object') {
        throw new TypeError('Claimant profile is required');
      }

      const hasVoice = !!profile.phone;
      const hasSMS = !!profile.phone && profile.smsOptIn;

      return { hasContactMethod: hasVoice || hasSMS };
    } catch (error) {
      verificationLogger.error(
        'Contact method verification failed due to unexpected error',
        error,
        {
          path: '323-fail-verification-when-no-contact-method',
          resource: 'db-j6x9',
        },
      );

      throw VerificationErrors.INTERNAL_VALIDATION_ERROR(
        `Internal validation error during contact method check: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
