/**
 * ClaimDraftingStateVerifier - Validates business rule conditions
 * for claim and drafting workflow states during verification timeout.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * Ensures that when a verification times out, the claim is set to
 * "Unverified" and the drafting workflow is set to "On Hold".
 */

import type { Claim } from '@/server/data_structures/Claim';
import type { DraftingWorkflow } from '@/server/data_structures/DraftingWorkflow';
import { DomainErrors } from '@/server/error_definitions/DomainErrors';

export interface StateValidationSuccess {
  valid: true;
}

export interface StateValidationFailure {
  valid: false;
  errors: string[];
}

export type StateValidationResult = StateValidationSuccess | StateValidationFailure;

export const ClaimDraftingStateVerifier = {
  /**
   * Validate that claim status is 'UNVERIFIED' after timeout enforcement.
   *
   * @throws DomainErrors.VALIDATION_ERROR if claim status is not UNVERIFIED
   */
  validateClaimStatus(claim: Claim): void {
    if (claim.status !== 'UNVERIFIED') {
      throw DomainErrors.VALIDATION_ERROR(
        `Expected claim status 'UNVERIFIED', found '${claim.status}'`,
      );
    }
  },

  /**
   * Validate that drafting workflow status is 'On Hold' after timeout enforcement.
   *
   * @throws DomainErrors.VALIDATION_ERROR if drafting status is not 'On Hold'
   */
  validateDraftingStatus(drafting: DraftingWorkflow): void {
    if (drafting.status !== 'On Hold') {
      throw DomainErrors.VALIDATION_ERROR(
        `Expected drafting status 'On Hold', found '${drafting.status}'`,
      );
    }
  },

  /**
   * Run all state validations for claim and drafting workflow.
   *
   * @throws DomainErrors.VALIDATION_ERROR on any validation failure
   */
  validate(claim: Claim, drafting: DraftingWorkflow): void {
    this.validateClaimStatus(claim);
    this.validateDraftingStatus(drafting);
  },
} as const;
