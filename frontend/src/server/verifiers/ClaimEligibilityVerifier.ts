/**
 * ClaimEligibilityVerifier - Validates that required claim categories
 * are present and all claims have unverified status.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 321-verify-key-claims-via-voice-or-sms
 */

import type { ClaimRecord, ClaimCategory } from '@/server/data_structures/ClaimRecord';
import { REQUIRED_CLAIM_CATEGORIES } from '@/server/data_structures/ClaimRecord';
import { VerificationErrors } from '@/server/error_definitions/VerificationErrors';

export interface VerificationSuccess {
  valid: true;
}

export interface VerificationFailure {
  valid: false;
  errors: string[];
}

export type VerificationResult = VerificationSuccess | VerificationFailure;

export const ClaimEligibilityVerifier = {
  /**
   * Validate that all required claim categories are present.
   *
   * Required categories: metrics, scope, production, security
   * @throws VerificationErrors.CLAIM_ELIGIBILITY_ERROR if any are missing
   */
  validateRequiredCategories(claims: ClaimRecord[]): void {
    const presentCategories = new Set(claims.map(c => c.category));
    const missingCategories = REQUIRED_CLAIM_CATEGORIES.filter(
      cat => !presentCategories.has(cat),
    );

    if (missingCategories.length > 0) {
      throw VerificationErrors.CLAIM_ELIGIBILITY_ERROR(
        `Missing required claim categories: ${missingCategories.join(', ')}`,
      );
    }
  },

  /**
   * Validate that all claims have unverified status.
   *
   * @throws VerificationErrors.CLAIM_ELIGIBILITY_ERROR if any are not unverified
   */
  validateUnverifiedStatus(claims: ClaimRecord[]): void {
    const nonUnverified = claims.filter(c => c.status !== 'unverified');

    if (nonUnverified.length > 0) {
      throw VerificationErrors.CLAIM_ELIGIBILITY_ERROR(
        `Claims must have unverified status. Found ${nonUnverified.length} claim(s) with non-unverified status.`,
      );
    }
  },

  /**
   * Run all eligibility validations.
   *
   * @throws VerificationErrors.CLAIM_ELIGIBILITY_ERROR on any validation failure
   */
  validate(claims: ClaimRecord[]): void {
    if (claims.length === 0) {
      throw VerificationErrors.CLAIM_ELIGIBILITY_ERROR(
        'No claims found for verification',
      );
    }

    this.validateRequiredCategories(claims);
    this.validateUnverifiedStatus(claims);
  },
} as const;
