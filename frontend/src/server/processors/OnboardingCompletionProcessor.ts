/**
 * OnboardingCompletionProcessor - Coordinates business logic for onboarding
 * completion and KPI analytics event creation.
 *
 * Resource: db-b7r2 (processor)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * Orchestration:
 * 1. Verify eligibility and update onboarding state (Step 3)
 * 2. Construct analytics event with KPI identifier (Step 4)
 * 3. Persist analytics event (Step 5)
 * 4. Return success response (Step 6)
 *
 * Error handling:
 * - Eligibility/persistence failure → BackendErrors, no analytics event
 * - KPI identifier missing → BackendErrors.KpiIdentifierMissing
 * - Analytics persistence failure → logged, onboarding remains successful
 */

import { OnboardingService } from '@/server/services/OnboardingService';
import { OnboardingDao } from '@/server/data_access_objects/OnboardingDao';
import { BackendErrors } from '@/server/error_definitions/BackendErrors';
import { getKpiForStep } from '@/shared/constants/LeadingKpis';
import { onboardingLogger } from '@/server/logging/onboardingLogger';
import type { OnboardingCompletionResult } from '@/server/data_structures/Onboarding';
import type { AnalyticsEvent } from '@/server/data_structures/AnalyticsEvent';

export interface ProcessResult {
  status: 'completed';
  onboardingId: string;
  step: number;
  analyticsRecorded: boolean;
}

export const OnboardingCompletionProcessor = {
  /**
   * Process the full onboarding completion + analytics recording flow.
   *
   * Steps:
   * 1. Complete onboarding step via service
   * 2. Construct analytics event
   * 3. Persist analytics event
   * 4. Return result with analytics status
   */
  async process(
    userId: string,
    step: number,
    metadata?: Record<string, unknown>,
  ): Promise<ProcessResult> {
    // Step 3: Business logic confirms successful action
    const completionResult = await OnboardingService.completeStep(userId, step);

    // Step 4: Construct leading KPI analytics event
    const analyticsEvent = this.constructAnalyticsEvent(
      completionResult,
      metadata,
    );

    // Step 5: Persist analytics event (non-fatal on failure)
    let analyticsRecorded = false;
    try {
      await OnboardingDao.insertAnalyticsEvent(analyticsEvent);
      analyticsRecorded = true;

      onboardingLogger.info('Analytics event recorded successfully', {
        userId,
        step,
        kpiId: analyticsEvent.kpiId,
      });
    } catch (error) {
      // Analytics persistence failure is non-fatal
      // Onboarding completion remains successful
      onboardingLogger.error(
        'Failed to persist analytics event',
        error,
        {
          userId,
          step,
          kpiId: analyticsEvent.kpiId,
        },
      );
    }

    // Step 6: Return success
    return {
      status: 'completed',
      onboardingId: completionResult.id,
      step: completionResult.step,
      analyticsRecorded,
    };
  },

  /**
   * Construct an analytics event from a completion result.
   * Throws BackendErrors.KpiIdentifierMissing if KPI mapping not found.
   */
  constructAnalyticsEvent(
    completionResult: OnboardingCompletionResult,
    metadata?: Record<string, unknown>,
  ): { kpiId: string; userId: string; timestamp: string; metadata: Record<string, unknown> } {
    const kpiId = getKpiForStep(completionResult.step);

    if (!kpiId) {
      throw BackendErrors.KpiIdentifierMissing(
        `No KPI identifier found for onboarding step ${completionResult.step}`,
      );
    }

    return {
      kpiId,
      userId: completionResult.userId,
      timestamp: completionResult.completedAt,
      metadata: {
        step: completionResult.step,
        ...metadata,
      },
    };
  },

  /**
   * Check idempotency - if analytics event already exists for this action,
   * skip creation and return success.
   */
  async checkIdempotency(
    userId: string,
    kpiId: string,
    step: number,
  ): Promise<boolean> {
    try {
      const existing = await OnboardingDao.findAnalyticsEvent(userId, kpiId, {
        step,
      });
      return existing !== null;
    } catch {
      return false;
    }
  },
} as const;
