/**
 * FinalizedAnswerVerifier - Ensures answer is finalized and locked before
 * allowing export or copy.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 334-export-or-copy-finalized-answer
 *
 * Checks:
 * 1. Answer must be finalized (finalized === true)
 * 2. Answer must be locked (locked === true)
 *
 * Throws AnswerErrors.AnswerNotLocked if either condition fails.
 */

import type { Answer } from '@/server/data_structures/Answer';
import { AnswerErrors } from '@/server/error_definitions/AnswerErrors';

export const FinalizedAnswerVerifier = {
  /**
   * Assert that the answer is finalized and locked for export.
   *
   * @throws AnswerErrors.AnswerNotLocked if not finalized or not locked
   */
  ensureFinalizedLocked(answer: Answer): void {
    if (!answer.finalized || !answer.locked) {
      throw AnswerErrors.AnswerNotLocked(
        `Answer '${answer.id}' is not finalized and locked (finalized=${answer.finalized}, locked=${answer.locked})`,
      );
    }
  },
} as const;
