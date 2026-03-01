/**
 * FollowupSmsProcessChain - Orchestrates the SMS follow-up workflow
 * from claim eligibility validation through SMS send.
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * Steps:
 * 1. Validate claim eligibility (status === 'UNCERTAIN', smsOptIn === true)
 * 2. Send follow-up SMS via SmsFollowupService
 */

import type { FollowupSmsEvent, ClaimEligibilityResult, SmsSendResult } from '@/server/data_structures/Claim';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { ClaimSchema } from '@/server/data_structures/Claim';
import { BackendErrors } from '@/server/error_definitions/SmsErrors';
import { SmsFollowupService } from '@/server/services/SmsFollowupService';
import { smsLogger } from '@/server/logging/smsLogger';

export const FollowupSmsProcessChain = {
  /**
   * Start the follow-up SMS process chain.
   *
   * @param event - Contains claimId to process
   */
  async start(event: { claimId: string }): Promise<void> {
    // Step 2: Validate claim eligibility
    const eligibility = await this.validateEligibility(event.claimId);

    if (!eligibility.eligible) {
      smsLogger.info('Claim ineligible for SMS follow-up', {
        claimId: event.claimId,
        reason: eligibility.reason,
      });
      return;
    }

    // Step 3: Send follow-up SMS
    await SmsFollowupService.sendFollowup(eligibility.claim);
  },

  /**
   * Step 2: Validate claim eligibility for SMS follow-up.
   *
   * Loads claim from DAO and checks:
   * - status === 'UNCERTAIN'
   * - smsOptIn === true
   *
   * @throws BackendErrors.CLAIM_LOAD_FAILED on DAO failure
   */
  async validateEligibility(claimId: string): Promise<ClaimEligibilityResult> {
    let claim;

    try {
      claim = await ClaimDAO.findById(claimId);
    } catch (error) {
      smsLogger.error('Failed to load claim for eligibility check', error, { claimId });
      throw BackendErrors.CLAIM_LOAD_FAILED(
        `Failed to load claim ${claimId}: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }

    if (!claim) {
      smsLogger.error('Claim not found for eligibility check', undefined, { claimId });
      throw BackendErrors.CLAIM_LOAD_FAILED(`Claim ${claimId} not found`);
    }

    // Validate the claim shape
    const parsed = ClaimSchema.safeParse(claim);
    if (!parsed.success) {
      smsLogger.error('Claim data does not match expected schema', undefined, {
        claimId,
        issues: parsed.error.issues.map(i => i.message).join(', '),
      });
      throw BackendErrors.CLAIM_LOAD_FAILED(`Claim ${claimId} has invalid data`);
    }

    // Check eligibility conditions
    if (parsed.data.status !== 'UNCERTAIN') {
      return { eligible: false, reason: `Claim status is ${parsed.data.status}, expected UNCERTAIN` };
    }

    if (!parsed.data.smsOptIn) {
      return { eligible: false, reason: 'User has not opted in to SMS' };
    }

    return { eligible: true, claim: parsed.data };
  },
} as const;
