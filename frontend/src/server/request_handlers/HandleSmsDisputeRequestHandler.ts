/**
 * HandleSmsDisputeRequestHandler - Transforms validated dispute webhook data
 * into a service invocation for claim dispute handling.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 322-handle-disputed-claims-and-block-drafting
 *
 * Known errors (DisputeError) are rethrown as-is.
 * Unknown errors are logged and wrapped in DisputeErrors.SERVICE_INVOCATION_FAILED.
 */

import { ClaimDisputeService } from '@/server/services/ClaimDisputeService';
import { DisputeError, DisputeErrors } from '@/server/error_definitions/DisputeErrors';
import { logger } from '@/server/logging/logger';
import type { SmsDisputePayload } from '@/server/endpoints/smsDisputeWebhook';
import type { DisputeResult } from '@/server/services/ClaimDisputeService';

export const HandleSmsDisputeRequestHandler = {
  /**
   * Handle an SMS dispute request by delegating to ClaimDisputeService.
   *
   * @param payload - Structured dispute payload { claimantId, disputedClaimIds }
   * @returns DisputeResult with updated claims and case blocked status
   * @throws DisputeError for known errors (rethrown)
   * @throws DisputeError SERVICE_INVOCATION_FAILED for unexpected errors
   */
  async handle(payload: SmsDisputePayload): Promise<DisputeResult> {
    try {
      const result = await ClaimDisputeService.handleDispute(
        payload.claimantId,
        payload.disputedClaimIds,
      );

      return result;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof DisputeError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during SMS dispute handling',
        error,
        {
          path: '322-handle-disputed-claims-and-block-drafting',
          resource: 'api-n8k2',
        },
      );

      throw DisputeErrors.SERVICE_INVOCATION_FAILED(
        `Failed to invoke dispute handling service: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
