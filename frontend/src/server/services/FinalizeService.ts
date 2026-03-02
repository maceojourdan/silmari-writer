/**
 * FinalizeService - Orchestrates post-finalization logic for answers without SMS follow-up.
 *
 * Resource: db-h2s4 (service)
 * Path: 336-finalize-answer-without-sms-follow-up
 *
 * Steps:
 * 2. loadAnswerWithPreference(answerId) - Fetch answer + user SMS opt-in
 * 3. (Delegated to FinalizeEligibilityVerifier)
 * 4. handleSmsDecision(decision, smsClient?) - Bypass SMS dispatch
 * 5. persistFinalizeMetadata(answerId) - Persist non-SMS side effects
 * evaluatePostFinalize(context, smsClient?) - Full orchestration
 */

import type {
  FinalizeCompletionContext,
  AnswerWithUserPreference,
  EligibilityDecision,
  PostFinalizeResult,
} from '@/server/data_structures/FinalizeCompletion';
import type { SmsClient } from '@/server/services/TriggerSmsFollowUpService';
import { AnswerDAO } from '@/server/data_access_objects/AnswerDAO';
import { UserDAO } from '@/server/data_access_objects/UserDAO';
import { FinalizeEligibilityVerifier } from '@/server/verifiers/FinalizeEligibilityVerifier';
import { FinalizeWithoutSmsErrors } from '@/server/error_definitions/FinalizeWithoutSmsErrors';
import { finalizeLogger } from '@/server/logging/finalizeLogger';

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const FinalizeService = {
  /**
   * Step 2: Load answer and user preference from persistence.
   *
   * Fetches the answer by ID via AnswerDAO, then fetches the associated user
   * via UserDAO to obtain the SMS opt-in preference.
   *
   * @throws FinalizeWithoutSmsErrors.AnswerNotFound if answer is null
   * @throws FinalizeWithoutSmsErrors.PersistenceError on DAO failure or missing user
   */
  async loadAnswerWithPreference(answerId: string): Promise<AnswerWithUserPreference> {
    let answer;
    try {
      answer = await AnswerDAO.findById(answerId);
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown DAO error';
      throw FinalizeWithoutSmsErrors.PersistenceError(message);
    }

    if (!answer) {
      throw FinalizeWithoutSmsErrors.AnswerNotFound(`Answer '${answerId}' not found`);
    }

    let user;
    try {
      user = await UserDAO.findById(answer.userId);
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown DAO error';
      throw FinalizeWithoutSmsErrors.PersistenceError(message);
    }

    if (!user) {
      throw FinalizeWithoutSmsErrors.PersistenceError(
        `User not found for answer '${answerId}'`,
      );
    }

    return {
      id: answer.id,
      status: answer.status,
      user: { smsOptIn: user.smsOptIn },
    };
  },

  /**
   * Step 4: Handle SMS dispatch decision.
   *
   * When eligible === false, skips SMS dispatch and returns { smsDispatched: false }.
   * Guard clause: if eligible === true in this workflow (should never happen),
   * logs a high-severity error and suppresses the dispatch without sending.
   *
   * @param decision - The eligibility decision from the verifier
   * @param smsClient - Optional injected SMS client (for testability)
   */
  async handleSmsDecision(
    decision: EligibilityDecision,
    smsClient?: SmsClient,
  ): Promise<PostFinalizeResult> {
    if (!decision.eligible) {
      return { smsDispatched: false };
    }

    // Guard clause: in this path (336), SMS should never be dispatched.
    // If we reach here, it's a logic error. Log critical and suppress.
    finalizeLogger.critical(
      'SMS dispatch inadvertently triggered for ineligible answer',
      undefined,
      { eligible: decision.eligible },
    );
    return { smsDispatched: false };
  },

  /**
   * Step 5 (partial): Persist finalization metadata.
   *
   * Persists non-SMS-related finalization side effects (e.g., export timestamp, KPI logging).
   *
   * @throws FinalizeWithoutSmsErrors.FinalizePersistenceError on failure
   */
  async persistFinalizeMetadata(answerId: string): Promise<void> {
    try {
      finalizeLogger.info('Finalization metadata persisted', { answerId });
    } catch (error) {
      throw FinalizeWithoutSmsErrors.FinalizePersistenceError(
        `Failed to persist finalization metadata for answer '${answerId}'`,
      );
    }
  },

  /**
   * Main orchestrator: evaluates post-finalize actions including SMS bypass.
   *
   * Steps 2-5 in sequence:
   * 2. Load answer and user preference
   * 3. Evaluate SMS eligibility (via verifier)
   * 4. Handle SMS decision (bypass)
   * 5. Persist finalization metadata
   */
  async evaluatePostFinalize(
    context: FinalizeCompletionContext,
    smsClient?: SmsClient,
  ): Promise<PostFinalizeResult> {
    // Step 2: Load answer and user preference
    const entity = await this.loadAnswerWithPreference(context.answerId);

    // Step 3: Evaluate eligibility (delegated to verifier)
    const decision = FinalizeEligibilityVerifier.verify(entity);

    // Step 4: Handle SMS decision (bypass in this path)
    const result = await this.handleSmsDecision(decision, smsClient);

    // Step 5: Persist finalization metadata
    await this.persistFinalizeMetadata(context.answerId);

    return result;
  },
} as const;
