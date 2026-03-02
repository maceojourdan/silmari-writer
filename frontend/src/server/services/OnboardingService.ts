/**
 * OnboardingService - Encapsulates onboarding domain logic.
 *
 * Resource: db-h2s4 (service)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * Responsibilities:
 * - Check user eligibility for step completion
 * - Update onboarding step status
 *
 * Throws BackendErrors on failure.
 */

import { OnboardingDao } from '@/server/data_access_objects/OnboardingDao';
import { BackendErrors } from '@/server/error_definitions/BackendErrors';
import type { OnboardingCompletionResult } from '@/server/data_structures/Onboarding';

export const OnboardingService = {
  /**
   * Check if a user is eligible to complete a given onboarding step.
   * A user is eligible if the step has not already been completed.
   *
   * Returns true if eligible, throws BackendErrors.StepAlreadyCompleted if not.
   */
  async isEligible(userId: string, step: number): Promise<boolean> {
    const existing = await OnboardingDao.findByUserAndStep(userId, step);

    if (existing && existing.status === 'COMPLETED') {
      throw BackendErrors.StepAlreadyCompleted(
        `Onboarding step ${step} already completed for user '${userId}'`,
      );
    }

    return true;
  },

  /**
   * Complete an onboarding step for a user.
   *
   * 1. Check eligibility
   * 2. Update step status to COMPLETED
   * 3. Return completion result
   *
   * Throws BackendErrors.StepAlreadyCompleted if already done.
   * Throws BackendErrors.PersistenceFailed on DB failure.
   */
  async completeStep(
    userId: string,
    step: number,
  ): Promise<OnboardingCompletionResult> {
    // Step 1: Check eligibility
    await this.isEligible(userId, step);

    // Step 2: Update step status
    const now = new Date().toISOString();

    try {
      const updated = await OnboardingDao.updateOnboardingStep(userId, step, {
        status: 'COMPLETED',
        completedAt: now,
        updatedAt: now,
      });

      // Step 3: Return completion result
      return {
        id: updated.id,
        userId: updated.userId,
        step: updated.step,
        status: 'COMPLETED',
        completedAt: updated.completedAt!,
      };
    } catch (error) {
      // If it's already a BackendError, rethrow
      if (error instanceof Error && error.name === 'BackendError') {
        throw error;
      }

      throw BackendErrors.PersistenceFailed(
        `Failed to persist onboarding step ${step} completion for user '${userId}'`,
      );
    }
  },
} as const;
