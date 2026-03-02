/**
 * FinalizeAnswerProcessor - Coordinates the finalize operation by delegating
 * to AnswerFinalizeService.
 *
 * Resource: db-b7r2 (processor)
 * Path: 333-finalize-answer-locks-editing
 */

import { AnswerFinalizeService } from '@/server/services/AnswerFinalizeService';
import type { FinalizeAnswerResult } from '@/server/data_structures/Answer';

export const FinalizeAnswerProcessor = {
  /**
   * Process the finalize operation for an answer.
   *
   * 1. Delegate to AnswerFinalizeService.finalize()
   * 2. Return the finalized result
   */
  async process(answerId: string): Promise<FinalizeAnswerResult> {
    return AnswerFinalizeService.finalize(answerId);
  },
} as const;
