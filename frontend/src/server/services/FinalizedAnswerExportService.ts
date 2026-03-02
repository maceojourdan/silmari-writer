/**
 * FinalizedAnswerExportService - Orchestrates validation and retrieval
 * of finalized answer content for export or copy.
 *
 * Resource: db-h2s4 (service)
 * Path: 334-export-or-copy-finalized-answer
 *
 * 1. Retrieve answer via DAO
 * 2. Verify finalized and locked via FinalizedAnswerVerifier
 * 3. Return full answer content
 *
 * Throws AnswerErrors on failure.
 */

import { AnswerDAO } from '@/server/data_access_objects/AnswerDAO';
import { FinalizedAnswerVerifier } from '@/server/verifiers/FinalizedAnswerVerifier';
import { AnswerErrors } from '@/server/error_definitions/AnswerErrors';
import type { Answer } from '@/server/data_structures/Answer';

export const FinalizedAnswerExportService = {
  /**
   * Retrieve a finalized and locked answer for export.
   *
   * 1. Load answer via DAO
   * 2. Verify finalized + locked state
   * 3. Return full answer
   *
   * @throws AnswerErrors.AnswerNotFound if answer doesn't exist
   * @throws AnswerErrors.AnswerNotLocked if not finalized or not locked
   */
  async getFinalizedAnswer(answerId: string): Promise<Answer> {
    // Step 1: Load answer
    const answer = await AnswerDAO.findById(answerId);

    if (!answer) {
      throw AnswerErrors.AnswerNotFound(
        `Answer '${answerId}' not found`,
      );
    }

    // Step 2: Verify finalized and locked
    FinalizedAnswerVerifier.ensureFinalizedLocked(answer);

    // Step 3: Return full answer
    return answer;
  },
} as const;
