/**
 * ExportFinalizedAnswerHandler - Maps incoming export/copy request to backend
 * service logic for retrieving finalized answer content.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 334-export-or-copy-finalized-answer
 *
 * Known errors (AnswerError) are rethrown as-is.
 * Unknown errors are wrapped in AnswerErrors.AnswerNotFound.
 */

import { FinalizedAnswerExportService } from '@/server/services/FinalizedAnswerExportService';
import { AnswerError, AnswerErrors } from '@/server/error_definitions/AnswerErrors';
import type { Answer } from '@/server/data_structures/Answer';
import { frontendLogger } from '@/logging/index';

export const ExportFinalizedAnswerHandler = {
  /**
   * Handle the export finalized answer flow:
   * 1. Delegate to service for validation + retrieval
   * 2. Return the full answer
   *
   * Known AnswerErrors are rethrown.
   * Unknown errors are logged and wrapped.
   */
  async handle(answerId: string): Promise<Answer> {
    try {
      const result = await FinalizedAnswerExportService.getFinalizedAnswer(answerId);
      return result;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof AnswerError) {
        throw error;
      }

      // Unknown errors → log and wrap
      frontendLogger.error(
        'Unexpected error during finalized answer export',
        error,
        { component: 'ExportFinalizedAnswerHandler', action: 'handle' },
      );

      throw AnswerErrors.AnswerNotFound(
        `Failed to export answer: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
