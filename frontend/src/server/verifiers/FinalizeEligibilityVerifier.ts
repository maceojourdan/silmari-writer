/**
 * FinalizeEligibilityVerifier - Validates finalized status and evaluates SMS opt-in.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import type {
  AnswerWithUserPreference,
  EligibilityDecision,
} from '@/server/data_structures/FinalizeCompletion';
import { FinalizeWithoutSmsErrors } from '@/server/error_definitions/FinalizeWithoutSmsErrors';

export const FinalizeEligibilityVerifier = {
  /**
   * Verify that the answer is in FINALIZED state and determine SMS eligibility.
   *
   * @param answer - The answer entity enriched with user preference data.
   * @returns An EligibilityDecision indicating whether SMS follow-up is eligible.
   * @throws FinalizeWithoutSmsErrors.InvalidFinalizeState if status !== 'FINALIZED'.
   */
  verify(answer: AnswerWithUserPreference): EligibilityDecision {
    if (answer.status !== 'FINALIZED') {
      throw FinalizeWithoutSmsErrors.InvalidFinalizeState(
        `Answer '${answer.id}' is in '${answer.status}' state, expected 'FINALIZED'`,
      );
    }

    return { eligible: answer.user.smsOptIn === true };
  },
} as const;
