/**
 * CompleteOnboardingStepHandler - Bridges endpoint to processor logic
 * for onboarding step completion.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * Known errors (BackendError) are rethrown as-is.
 * Unknown errors are wrapped in BackendErrors.SerializationError.
 */

import {
  OnboardingCompletionProcessor,
  type ProcessResult,
} from '@/server/processors/OnboardingCompletionProcessor';
import {
  BackendError,
  BackendErrors,
} from '@/server/error_definitions/BackendErrors';
import { onboardingLogger } from '@/server/logging/onboardingLogger';

export const CompleteOnboardingStepHandler = {
  /**
   * Handle the full onboarding completion flow:
   * 1. Delegate to processor for business logic + analytics
   * 2. Return the process result
   *
   * Known BackendErrors are rethrown.
   * Unknown errors are wrapped as SERIALIZATION_ERROR.
   */
  async handle(
    userId: string,
    step: number,
    metadata?: Record<string, unknown>,
  ): Promise<ProcessResult> {
    try {
      const result = await OnboardingCompletionProcessor.process(
        userId,
        step,
        metadata,
      );
      return result;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof BackendError) {
        throw error;
      }

      // Unknown errors → log and wrap
      onboardingLogger.error('Unexpected error during onboarding completion', error, {
        resource: 'api-n8k2',
        userId,
        step,
      });

      throw BackendErrors.SerializationError(
        `Failed to complete onboarding step: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
