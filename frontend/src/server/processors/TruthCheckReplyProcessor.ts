/**
 * TruthCheckReplyProcessor - Processes structured truth-check updates
 * by persisting the reply into the claim's truth_checks and updating status.
 *
 * Resource: db-b7r2 (processor)
 * Path: 305-followup-sms-for-uncertain-claim
 */

import type { Claim, TruthCheckUpdateRequest } from '@/server/data_structures/Claim';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { BackendErrors } from '@/server/error_definitions/SmsErrors';
import { smsLogger } from '@/server/logging/smsLogger';

export const TruthCheckReplyProcessor = {
  /**
   * Process a structured truth-check update request.
   *
   * 1. Persist the verdict into the claim's truth_checks via ClaimDAO
   * 2. Update claim status accordingly
   * 3. Return the updated claim record
   *
   * @throws BackendErrors.TRUTH_CHECK_PERSIST_FAILED on DAO failure
   */
  async process(update: TruthCheckUpdateRequest): Promise<Claim> {
    try {
      const updatedClaim = await ClaimDAO.updateTruthCheck(
        update.claimId,
        update.verdict,
        update.source,
      );

      smsLogger.info('Truth check updated successfully', {
        claimId: update.claimId,
        verdict: update.verdict,
        newStatus: updatedClaim.status,
      });

      return updatedClaim;
    } catch (error) {
      smsLogger.error('Failed to persist truth check update', error, {
        claimId: update.claimId,
        verdict: update.verdict,
      });

      throw BackendErrors.TRUTH_CHECK_PERSIST_FAILED(
        `Failed to persist truth check for claim ${update.claimId}: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
