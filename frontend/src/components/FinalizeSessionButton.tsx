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
        className="flex flex-col gap-2 p-4 bg-green-50 border border-green-200 rounded-md"
        data-testid="finalize-success"
      >
        <span className="text-green-700 font-medium">Session finalized</span>
        <span className="text-sm text-green-600">
          Session state: {result.sessionState}
        </span>
        <span className="text-sm text-green-600">
          StoryRecord status: {result.storyRecordStatus}
        </span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        onClick={handleFinalize}
        disabled={isLoading}
        aria-label="Finalize Session"
      >
        {isLoading ? 'Finalizing...' : 'Finalize Session'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}

      {showRetry && (
        <button
          className="text-sm text-blue-600 underline hover:text-blue-800"
          onClick={handleFinalize}
          aria-label="Retry"
        >
          Retry
        </button>
      )}
    </div>
  );
}
