'use client';

/**
 * OnboardingStepOne - Captures user action for onboarding step 1 completion
 * and displays confirmation.
 *
 * Resource: ui-w8p2 (component)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * On complete:
 *   1. Validate via OnboardingCompletionVerifier
 *   2. If invalid → display errors, do not call API
 *   3. If valid → call CompleteOnboardingStep({ userId, step: 1, metadata })
 *   4. On success → invoke onCompleted callback
 *   5. On error → display error message
 */

import { useState, useCallback } from 'react';
import { completeOnboardingStep } from '@/api_contracts/CompleteOnboardingStep';
import type { CompleteOnboardingStepResponse } from '@/api_contracts/CompleteOnboardingStep';
import { validateOnboardingCompletion } from '@/verifiers/OnboardingCompletionVerifier';

export interface OnboardingStepOneProps {
  userId: string;
  onCompleted?: (response: CompleteOnboardingStepResponse) => void;
}

export default function OnboardingStepOne({
  userId,
  onCompleted,
}: OnboardingStepOneProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isCompleted, setIsCompleted] = useState(false);

  const handleComplete = useCallback(async () => {
    setError(null);

    // Step 1: Validate input
    const validation = validateOnboardingCompletion(userId, 1);

    if (!validation.valid) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 2: Call API contract
    setIsLoading(true);
    try {
      const result = await completeOnboardingStep({
        userId: validation.payload.userId,
        step: validation.payload.step,
        metadata: validation.payload.metadata,
      });
      setIsCompleted(true);
      onCompleted?.(result);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
    } finally {
      setIsLoading(false);
    }
  }, [userId, onCompleted]);

  if (isCompleted) {
    return (
      <div
        className="flex items-center gap-2 text-green-600"
        data-testid="onboarding-success"
      >
        <span>Onboarding step 1 completed successfully.</span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <button
        className={`flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md transition-colors ${
          isLoading
            ? 'opacity-50 cursor-not-allowed bg-primary text-primary-foreground'
            : 'bg-primary text-primary-foreground hover:bg-primary/90'
        }`}
        onClick={handleComplete}
        disabled={isLoading}
        aria-label="Complete Onboarding Step"
      >
        {isLoading ? 'Completing...' : 'Complete Step 1'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
