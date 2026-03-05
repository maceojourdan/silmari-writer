'use client';

/**
 * FinalizeSessionButton - Captures user Finalize Session action.
 *
 * Resource: ui-w8p2 (component)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 *
 * On click:
 *   1. Verify session state is ACTIVE
 *   2. If valid → call finalizeSession API contract
 *   3. On success → display confirmation with session state and StoryRecord status
 *   4. On failure → log via frontendLogger and show retry prompt
 */

import { useState } from 'react';
import { finalizeSession, FinalizeSessionResponseSchema } from '@/api_contracts/finalizeSession';
import type { FinalizeSessionResponse } from '@/api_contracts/finalizeSession';
import { frontendLogger } from '@/logging/index';
import { Button } from '@/components/ui/button';

export interface FinalizeSessionButtonProps {
  sessionId: string;
  sessionState: string;
  onFinalized?: (result: FinalizeSessionResponse) => void;
}

export default function FinalizeSessionButton({
  sessionId,
  sessionState,
  onFinalized,
}: FinalizeSessionButtonProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [result, setResult] = useState<FinalizeSessionResponse | null>(null);
  const [showRetry, setShowRetry] = useState(false);

  const handleFinalize = async () => {
    setError(null);
    setShowRetry(false);

    // Step 1: Verify session state is ACTIVE
    if (sessionState !== 'ACTIVE') {
      setError(`Session must be in ACTIVE state to finalize. Current state: ${sessionState}`);
      return;
    }

    // Step 2: Call API contract
    setIsLoading(true);
    try {
      const finalizeResult = await finalizeSession({ sessionId });
      setResult(finalizeResult);
      onFinalized?.(finalizeResult);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
      setShowRetry(true);

      frontendLogger.error(
        'Failed to finalize session',
        err instanceof Error ? err : new Error(String(err)),
        { component: 'FinalizeSessionButton', action: 'finalize' },
      );
    } finally {
      setIsLoading(false);
    }
  };

  // Success state: show confirmation
  if (result) {
    return (
      <div
        className="flex flex-col gap-2 rounded-md border border-primary/30 bg-primary/10 p-4"
        data-testid="finalize-success"
      >
        <span className="font-medium text-primary">Session finalized</span>
        <span className="text-sm text-primary">
          Session state: {result.sessionState}
        </span>
        <span className="text-sm text-primary">
          StoryRecord status: {result.storyRecordStatus}
        </span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <Button
        onClick={handleFinalize}
        disabled={isLoading}
        aria-label="Finalize Session"
      >
        {isLoading ? 'Finalizing...' : 'Finalize Session'}
      </Button>

      {error && (
        <div className="text-sm text-destructive" role="alert">
          {error}
        </div>
      )}

      {showRetry && (
        <button
          className="text-sm text-primary underline underline-offset-4 hover:text-primary/90"
          onClick={handleFinalize}
          aria-label="Retry"
        >
          Retry
        </button>
      )}
    </div>
  );
}
