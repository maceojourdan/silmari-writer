/**
 * VerificationTimeoutService - Orchestrates the detection of expired
 * verification requests and enforcement of claim/drafting status changes.
 *
 * Resource: db-h2s4 (service)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * Steps:
 *   1. detectExpiredVerifications — find pending requests past timeout
 *   2. markAsTimedOut — persist timed-out status
 *   3. enforceUnverifiedAndOnHold — set claim/drafting states
 */

import { getVerificationTimeoutMs } from '@/server/settings/verificationTimeout';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { DraftingWorkflowDAO } from '@/server/data_access_objects/DraftingWorkflowDAO';
import { ClaimDraftingStateVerifier } from '@/server/verifiers/ClaimDraftingStateVerifier';
import { DomainErrors } from '@/server/error_definitions/DomainErrors';
import { logger } from '@/server/logging/logger';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';
import type { Claim } from '@/server/data_structures/Claim';
import type { DraftingWorkflow } from '@/server/data_structures/DraftingWorkflow';

const PATH = '324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold';
const RESOURCE = 'db-h2s4';

export const VerificationTimeoutService = {
  // -------------------------------------------------------------------------
  // Step 1: Detect verification timeout event
  // -------------------------------------------------------------------------

  /**
   * Identify voice/SMS verification requests that have exceeded the configured
   * timeout duration with no response received.
   *
   * @param now - The current timestamp for timeout comparison.
   * @returns List of expired VerificationRequest records.
   *
   * Error behavior:
   * - Config load failure → logs error and returns empty list.
   * - DAO failure → throws PersistenceError.
   */
  async detectExpiredVerifications(now: Date): Promise<VerificationRequest[]> {
    let timeoutMs: number;

    try {
      timeoutMs = getVerificationTimeoutMs();
    } catch (error) {
      logger.error(
        'Failed to load verification timeout config; skipping detection cycle',
        error,
        { path: PATH, resource: RESOURCE },
      );
      return [];
    }

    let pendingRequests: VerificationRequest[];

    try {
      pendingRequests = await VerificationRequestDAO.findPendingUnresponded();
    } catch (error) {
      throw DomainErrors.PERSISTENCE_ERROR(
        `Failed to query pending verification requests: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }

    // Filter: createdAt + timeout < now
    const cutoff = new Date(now.getTime() - timeoutMs);
    return pendingRequests.filter(
      (request) => new Date(request.createdAt).getTime() < cutoff.getTime(),
    );
  },

  // -------------------------------------------------------------------------
  // Step 2: Update verification status to timed-out
  // -------------------------------------------------------------------------

  /**
   * Persist status change for each expired verification request to "Timed Out".
   * Uses optimistic concurrency — if a response was recorded concurrently,
   * the record is skipped and the conflict is logged.
   *
   * @param records - Expired verification requests from Step 1.
   * @returns Successfully updated records.
   *
   * Error behavior:
   * - Concurrent response (0 affected rows) → log conflict, skip record.
   * - DAO failure → throws PersistenceError.
   */
  async markAsTimedOut(records: VerificationRequest[]): Promise<VerificationRequest[]> {
    const updated: VerificationRequest[] = [];

    for (const record of records) {
      try {
        const affectedRows = await VerificationRequestDAO.updateStatusIfUnresponded(
          record.id,
          'timed_out',
        );

        if (affectedRows === 0) {
          logger.warn(
            `Concurrency conflict: verification request ${record.id} was responded to before timeout update`,
            { path: PATH, resource: RESOURCE, requestId: record.id },
          );
          continue;
        }

        updated.push({
          ...record,
          status: 'timed_out',
          updatedAt: new Date().toISOString(),
        });
      } catch (error) {
        throw DomainErrors.PERSISTENCE_ERROR(
          `Failed to update verification request ${record.id}: ${error instanceof Error ? error.message : 'unknown'}`,
        );
      }
    }

    return updated;
  },

  // -------------------------------------------------------------------------
  // Step 3: Enforce claims remain unverified and drafting on hold
  // -------------------------------------------------------------------------

  /**
   * For each timed-out verification record, set the associated claim to
   * "Unverified" and the drafting workflow to "On Hold".
   *
   * @param records - Timed-out verification requests from Step 2.
   * @returns Array of { claim, drafting } pairs reflecting enforced state.
   *
   * Error behavior:
   * - Missing claim or drafting entity → throws DomainIntegrityError.
   * - Business rule validation failure → throws ValidationError.
   */
  async enforceUnverifiedAndOnHold(
    records: VerificationRequest[],
  ): Promise<Array<{ claim: Claim; drafting: DraftingWorkflow }>> {
    const results: Array<{ claim: Claim; drafting: DraftingWorkflow }> = [];

    for (const record of records) {
      for (const claimId of record.claimIds) {
        // Load claim
        const claim = await ClaimDAO.findById(claimId);
        if (!claim) {
          throw DomainErrors.DOMAIN_INTEGRITY_ERROR(
            `Claim ${claimId} not found for verification request ${record.id}`,
          );
        }

        // Load drafting workflow
        const drafting = await DraftingWorkflowDAO.findByClaimId(claimId);
        if (!drafting) {
          throw DomainErrors.DOMAIN_INTEGRITY_ERROR(
            `Drafting workflow not found for claim ${claimId}`,
          );
        }

        // Set statuses
        claim.status = 'UNVERIFIED';
        drafting.status = 'On Hold';
        drafting.reason = 'Verification timed out';

        // Validate via verifier
        ClaimDraftingStateVerifier.validate(claim, drafting);

        // Persist
        const updatedClaim = await ClaimDAO.updateStatus(claimId, 'UNVERIFIED');
        const updatedDrafting = await DraftingWorkflowDAO.updateStatus(
          drafting.id,
          'On Hold',
          'Verification timed out',
        );

        results.push({ claim: updatedClaim, drafting: updatedDrafting });
      }
    }

    return results;
  },
} as const;
