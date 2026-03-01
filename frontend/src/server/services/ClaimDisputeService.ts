/**
 * ClaimDisputeService - Orchestrates claim status updates and
 * drafting state transitions when claims are disputed.
 *
 * Resource: db-h2s4 (service)
 * Path: 322-handle-disputed-claims-and-block-drafting
 *
 * Steps:
 * 1. Mark each disputed claim as 'not_verified' (Step 3)
 * 2. Block drafting if any claim is not verified (Step 4)
 */

import { ClaimCaseDAO } from '@/server/data_access_objects/ClaimCaseDAO';
import { CaseStateVerifier } from '@/server/verifiers/CaseStateVerifier';
import { DisputeError, DisputeErrors } from '@/server/error_definitions/DisputeErrors';
import { logger } from '@/server/logging/logger';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';
import type { Case } from '@/server/data_structures/Case';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface DisputeResult {
  updatedClaims: ClaimRecord[];
  caseBlocked: boolean;
}

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const ClaimDisputeService = {
  /**
   * Handle a dispute by marking claims as not_verified and blocking drafting.
   *
   * @param claimantId - The claimant who is disputing
   * @param disputedClaimIds - IDs of claims being disputed
   * @returns DisputeResult with updated claims and case blocked status
   * @throws DisputeError CLAIM_NOT_FOUND if any claim ID is invalid
   * @throws DisputeError PERSISTENCE_ERROR if DAO update fails
   * @throws DisputeError INVALID_STATE_TRANSITION if drafting block is not allowed
   */
  async handleDispute(
    claimantId: string,
    disputedClaimIds: string[],
  ): Promise<DisputeResult> {
    const updatedClaims: ClaimRecord[] = [];
    const now = new Date().toISOString();

    // Step 3: Mark each disputed claim as not_verified
    for (const claimId of disputedClaimIds) {
      // Fetch the claim
      let claim: ClaimRecord | null;
      try {
        claim = await ClaimCaseDAO.getClaimById(claimId);
      } catch (error) {
        logger.error('Failed to fetch claim for dispute', error, {
          path: '322-handle-disputed-claims-and-block-drafting',
          resource: 'db-h2s4',
        });
        throw DisputeErrors.PERSISTENCE_ERROR(
          `Failed to fetch claim ${claimId}: ${error instanceof Error ? error.message : 'unknown'}`,
        );
      }

      if (!claim) {
        throw DisputeErrors.CLAIM_NOT_FOUND(
          `Disputed claim not found: ${claimId}`,
        );
      }

      // Update verification status
      let updatedClaim: ClaimRecord;
      try {
        updatedClaim = await ClaimCaseDAO.updateClaimVerificationStatus(
          claimId,
          'not_verified',
          now,
        );
      } catch (error) {
        logger.error('Failed to update claim verification status', error, {
          path: '322-handle-disputed-claims-and-block-drafting',
          resource: 'db-h2s4',
        });
        throw DisputeErrors.PERSISTENCE_ERROR(
          `Failed to update claim ${claimId}: ${error instanceof Error ? error.message : 'unknown'}`,
        );
      }

      updatedClaims.push(updatedClaim);
    }

    // Step 4: Block drafting process
    const caseRecord = await ClaimCaseDAO.getCaseByClaimantId(claimantId);

    if (!caseRecord) {
      throw DisputeErrors.CLAIM_NOT_FOUND(
        `No case found for claimant: ${claimantId}`,
      );
    }

    // Verify state transition is allowed
    const verificationResult = CaseStateVerifier.assertDraftingBlockAllowed(
      caseRecord.drafting_status,
    );

    if (!verificationResult.valid) {
      throw DisputeErrors.INVALID_STATE_TRANSITION(
        `Cannot block drafting: ${verificationResult.reason}`,
      );
    }

    // Update case drafting status
    try {
      await ClaimCaseDAO.updateCaseDraftingStatus(
        caseRecord.id,
        'blocked_due_to_unverified_claims',
      );
    } catch (error) {
      logger.error('Failed to update case drafting status', error, {
        path: '322-handle-disputed-claims-and-block-drafting',
        resource: 'db-h2s4',
      });
      throw DisputeErrors.PERSISTENCE_ERROR(
        `Failed to block drafting for case ${caseRecord.id}: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }

    logger.info('Dispute handled successfully', {
      path: '322-handle-disputed-claims-and-block-drafting',
      resource: 'db-h2s4',
    });

    return {
      updatedClaims,
      caseBlocked: true,
    };
  },
} as const;
