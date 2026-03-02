/**
 * FinalizeAnswerRequestHandler - Maps the answerId to the finalize flow
 * and delegates to AnswerFinalizeService.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 333-finalize-answer-locks-editing
 *
 * Known errors (FinalizeAnswerError) are rethrown as-is.
 * Unknown errors are wrapped in FinalizeAnswerErrors.SerializationError.
 */

import { AnswerFinalizeService } from '@/server/services/AnswerFinalizeService';
import { FinalizeAnswerError, FinalizeAnswerErrors } from '@/server/error_definitions/FinalizeAnswerErrors';
import type { FinalizeAnswerResult } from '@/server/data_structures/Answer';
import { logger } from '@/server/logging/logger';

export const FinalizeAnswerRequestHandler = {
  /**
   * Handle the full finalize-answer flow:
   * 1. Delegate to service for validation + persistence
   * 2. Return the finalized result
   *
   * Known FinalizeAnswerErrors are rethrown.
   * Unknown errors are wrapped as SERIALIZATION_ERROR.
   */
  async handle(answerId: string): Promise<FinalizeAnswerResult> {
    try {
      const result = await AnswerFinalizeService.finalize(answerId);
      return result;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof FinalizeAnswerError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during answer finalization',
        error,
        { path: '333-finalize-answer-locks-editing', resource: 'api-n8k2' },
      );

      throw FinalizeAnswerErrors.SerializationError(
        `Failed to finalize answer: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
