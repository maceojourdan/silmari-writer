/**
 * UpdateAnswerRequestHandler - Delegates answer content updates to AnswerService
 * and maps errors appropriately.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 337-prevent-edit-of-locked-answer
 *
 * Known errors (AnswerError) are rethrown as-is.
 * Unknown errors are wrapped in AnswerErrors.SerializationError.
 */

import { AnswerService } from '@/server/services/AnswerService';
import type { UpdateAnswerResult } from '@/server/services/AnswerService';
import { AnswerError, AnswerErrors } from '@/server/error_definitions/AnswerErrors';
import { logger } from '@/server/logging/logger';

export const UpdateAnswerRequestHandler = {
  /**
   * Handle an answer content update request:
   * 1. Delegate to AnswerService.updateAnswer(id, content)
   * 2. Known AnswerErrors are rethrown
   * 3. Unknown errors are logged and wrapped as SERIALIZATION_ERROR
   */
  async handle(id: string, content: string): Promise<UpdateAnswerResult> {
    try {
      const result = await AnswerService.updateAnswer(id, content);
      return result;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof AnswerError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during answer update',
        error,
        { path: '337-prevent-edit-of-locked-answer', resource: 'api-n8k2' },
      );

      throw AnswerErrors.SerializationError(
        `Failed to update answer: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
