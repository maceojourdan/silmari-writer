/**
 * FollowupSmsPattern - Evaluates whether an incoming event matches
 * the FOLLOWUP_SMS pattern and forwards to the backend process chain.
 *
 * Resource: mq-t2f7 (execution_pattern)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * If event.type === 'FOLLOWUP_SMS' and claimId is present,
 * dispatches to FollowupSmsProcessChain.start({ claimId }).
 * Otherwise, logs pattern_bypass via shared logger and returns BYPASS.
 */

import { FollowupSmsProcessChain } from '@/server/process_chains/FollowupSmsProcessChain';
import { frontendLogger } from '@/logging/index';

export type PatternResult = 'MATCHED' | 'BYPASS';

export const FollowupSmsPattern = {
  /**
   * Evaluate an event against the FOLLOWUP_SMS pattern.
   *
   * @param event - The incoming event to evaluate
   * @returns 'MATCHED' if pattern fires, 'BYPASS' otherwise
   */
  async evaluate(event: Record<string, unknown>): Promise<PatternResult> {
    // Guard: event must have type === 'FOLLOWUP_SMS' and a claimId
    if (
      typeof event !== 'object' ||
      event === null ||
      event.type !== 'FOLLOWUP_SMS' ||
      typeof event.claimId !== 'string' ||
      !event.claimId
    ) {
      frontendLogger.info('pattern_bypass: event does not match FOLLOWUP_SMS pattern', {
        path: '305-followup-sms-for-uncertain-claim',
        resource: 'cfg-p4b8',
        eventType: typeof event === 'object' && event !== null ? String(event.type) : 'unknown',
      });

      return 'BYPASS';
    }

    // Dispatch to backend process chain with only claimId
    await FollowupSmsProcessChain.start({ claimId: event.claimId as string });

    return 'MATCHED';
  },
} as const;
