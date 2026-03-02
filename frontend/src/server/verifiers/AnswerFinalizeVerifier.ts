/**
 * AnswerFinalizeVerifier - Validates that an answer is eligible for finalization.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 333-finalize-answer-locks-editing
 *
 * Ensures the answer is in COMPLETED status and not already finalized.
 * Throws FinalizeAnswerError on validation failure.
 */

import type { Answer } from '@/server/data_structures/Answer';
import { FinalizeAnswerErrors } from '@/server/error_definitions/FinalizeAnswerErrors';

export const AnswerFinalizeVerifier = {
  /**
   * Assert that the answer entity is eligible for finalization.
   *
   * Checks:
   * 1. Answer status must be COMPLETED
   * 2. Answer must not already be finalized
   *
   * @throws FinalizeAnswerErrors.AnswerNotCompleted if status !== COMPLETED
   * @throws FinalizeAnswerErrors.AnswerAlreadyFinalized if finalized === true
   */
  assertEligible(answer: Answer): void {
    if (answer.finalized) {
      throw FinalizeAnswerErrors.AnswerAlreadyFinalized(
        `Answer '${answer.id}' has already been finalized`,
      );
    }

    if (answer.status !== 'COMPLETED') {
      throw FinalizeAnswerErrors.AnswerNotCompleted(
        `Answer '${answer.id}' is in '${answer.status}' status, expected 'COMPLETED'`,
      );
    }
  },
} as const;
