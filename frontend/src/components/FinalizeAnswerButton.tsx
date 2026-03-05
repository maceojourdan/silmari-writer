'use client';

/**
 * FinalizeAnswerButton - Captures user Finalize action for completed answers.
 *
 * Resource: ui-w8p2 (component)
 * Path: 333-finalize-answer-locks-editing
 *
 * On click:
 *   1. If not editable → set error from SharedErrors.ANSWER_ALREADY_FINALIZED
 *   2. If editable → call finalizeAnswer({ answerId })
 *   3. On success → invoke onFinalized callback
 */

import { useState } from 'react';
import { finalizeAnswer } from '@/api_contracts/finalizeAnswer';
import type { FinalizeAnswerResponse } from '@/api_contracts/finalizeAnswer';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';
import { Button } from '@/components/ui/button';

export interface FinalizeAnswerButtonProps {
  answerId: string;
  editable: boolean;
  onFinalized?: (response: FinalizeAnswerResponse) => void;
}

export default function FinalizeAnswerButton({
  answerId,
  editable,
  onFinalized,
}: FinalizeAnswerButtonProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isFinalized, setIsFinalized] = useState(false);

  const handleFinalize = async () => {
    setError(null);

    // Step 1: Check editable — block if already finalized
    if (!editable) {
      const sharedError = SharedErrors.AnswerAlreadyFinalized();
      setError(sharedError.message);
      return;
    }

    // Step 2: Call API contract
    setIsLoading(true);
    try {
      const result = await finalizeAnswer({ answerId });
      setIsFinalized(true);
      onFinalized?.(result);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
    } finally {
      setIsLoading(false);
    }
  };

  if (isFinalized) {
    return (
      <div className="flex items-center gap-2 text-primary" data-testid="finalize-success">
        <span>Answer finalized successfully.</span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <Button
        onClick={handleFinalize}
        disabled={isLoading}
        aria-disabled={!editable}
        aria-label="Finalize Answer"
      >
        {isLoading ? 'Finalizing...' : 'Finalize Answer'}
      </Button>

      {error && (
        <div className="text-sm text-destructive" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
