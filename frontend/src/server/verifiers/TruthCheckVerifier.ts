/**
 * TruthCheckVerifier - Validates truth_check structure and claim eligibility.
 *
 * Ensures that each claim in truth_checks has valid structure before
 * filtering logic is applied.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { ClaimSchema, type Claim } from '@/server/data_structures/DraftStoryRecord';
import { DraftValidationError } from '@/server/error_definitions/DraftErrors';

export const TruthCheckVerifier = {
  /**
   * Validate the structure of a single claim.
   *
   * Uses Zod ClaimSchema to enforce required fields and types.
   * On failure, throws DraftValidationError.INVALID_TRUTH_CHECK.
   */
  validateStructure(claim: unknown): Claim {
    const result = ClaimSchema.safeParse(claim);

    if (!result.success) {
      throw DraftValidationError.INVALID_TRUTH_CHECK(
        `Invalid truth check structure: ${result.error.message}`,
      );
    }

    return result.data;
  },

  /**
   * Validate an array of claims, returning only structurally valid ones.
   *
   * Throws DraftValidationError.INVALID_TRUTH_CHECK on the first invalid claim.
   */
  validateAll(claims: unknown[]): Claim[] {
    return claims.map((claim) => this.validateStructure(claim));
  },
} as const;
