/**
 * BehavioralQuestionService - Orchestrates server-side validation and
 * state transition logic for behavioral questions.
 *
 * Resource: db-h2s4 (service)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Flow:
 * 1. Validate minimum slots via BehavioralQuestionMinimumSlotsVerifier
 * 2. If valid → persist state transition via BehavioralQuestionDAO
 * 3. If invalid → throw MinimumSlotsNotMetError
 */

import type { EvaluateCommand, EvaluateResult } from '@/server/data_structures/BehavioralQuestion';
import { BehavioralQuestionMinimumSlotsVerifier } from '@/server/verifiers/BehavioralQuestionMinimumSlotsVerifier';
import { BehavioralQuestionDAO } from '@/server/data_access_objects/BehavioralQuestionDAO';
import { BehavioralQuestionErrors } from '@/server/error_definitions/BehavioralQuestionErrors';

export const BehavioralQuestionService = {
  /**
   * Evaluate whether a behavioral question is eligible for VERIFY transition.
   *
   * 1. Re-validate minimum slot constraints server-side.
   * 2. If eligible → persist transition via DAO.updateStatus.
   * 3. Return eligibility result.
   */
  async evaluateForVerify(command: EvaluateCommand): Promise<EvaluateResult> {
    // Step 1: Server-side re-validation
    const verification = BehavioralQuestionMinimumSlotsVerifier.verify({
      objective: command.objective,
      actions: command.actions,
      obstacles: command.obstacles,
      outcome: command.outcome,
      roleClarity: command.roleClarity,
    });

    if (!verification.valid) {
      const errorDetails = Object.entries(verification.errors)
        .map(([field, msg]) => `${field}: ${msg}`)
        .join('; ');
      throw BehavioralQuestionErrors.MINIMUM_SLOTS_NOT_MET(
        `Minimum slot requirements not met: ${errorDetails}`,
      );
    }

    // Step 2: Persist state transition DRAFT → VERIFY
    try {
      const updated = await BehavioralQuestionDAO.updateStatus(
        command.sessionId,
        'VERIFY',
      );

      return {
        eligible: true,
        questionId: updated.id!,
        status: updated.status,
        updatedAt: updated.updatedAt || new Date().toISOString(),
      };
    } catch (error) {
      // If it's already a BehavioralQuestionError, re-throw
      if (error instanceof Error && error.name === 'BehavioralQuestionError') {
        throw error;
      }

      throw BehavioralQuestionErrors.PERSISTENCE_FAILED(
        `Failed to persist behavioral question: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },
} as const;
