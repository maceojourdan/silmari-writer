/**
 * SmsWebhookHandler - Orchestrates inbound SMS webhook processing:
 * parse payload, correlate to claim, forward to processor.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * Known errors (WebhookError, SmsError) are rethrown as-is.
 * Unknown errors are logged and wrapped in GenericErrors.InternalError.
 */

import { SmsReplyTransformer } from '@/server/transformers/SmsReplyTransformer';
import { TruthCheckReplyProcessor } from '@/server/processors/TruthCheckReplyProcessor';
import { WebhookError } from '@/server/error_definitions/WebhookErrors';
import { SmsError } from '@/server/error_definitions/SmsErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';
import type { Claim } from '@/server/data_structures/Claim';

export const SmsWebhookHandler = {
  /**
   * Handle an inbound SMS webhook request.
   *
   * 1. Parse and transform the raw payload via SmsReplyTransformer
   * 2. Forward structured update to TruthCheckReplyProcessor
   * 3. Return updated claim
   *
   * @param payload - Raw webhook body
   * @returns Updated claim record
   * @throws WebhookError for validation/correlation failures
   * @throws SmsError for persistence failures
   * @throws GenericError for unexpected failures
   */
  async handle(payload: unknown): Promise<Claim> {
    try {
      // Parse and correlate
      const update = await SmsReplyTransformer.parse(payload);

      // Process the truth check update
      const updatedClaim = await TruthCheckReplyProcessor.process(update);

      return updatedClaim;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof WebhookError || error instanceof SmsError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during SMS webhook processing',
        error,
        {
          path: '305-followup-sms-for-uncertain-claim',
          resource: 'api-n8k2',
        },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during SMS webhook processing: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
