/**
 * useSessionDataLoader - React hook that wraps the submitVoiceResponse API call
 * and manages session state updates.
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 307-process-voice-input-and-progress-session
 *
 * On success → updates session and storyRecord state.
 * On error → logs via frontendLogger and sets recoverable UI error state.
 */

import { useState, useCallback } from 'react';
import type { AnswerSession, AnswerStoryRecord } from '@/server/data_structures/AnswerSession';
import { submitVoiceResponse } from '@/api_contracts/submitVoiceResponse';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Hook Return Type
// ---------------------------------------------------------------------------

export interface UseSessionDataLoaderReturn {
  session: AnswerSession;
  storyRecord: AnswerStoryRecord | null;
  isSubmitting: boolean;
  error: string | null;
  submitTranscript: (transcript: string) => Promise<void>;
}

// ---------------------------------------------------------------------------
// Hook Implementation
// ---------------------------------------------------------------------------

export function useSessionDataLoader(
  initialSession: AnswerSession,
): UseSessionDataLoaderReturn {
  const [session, setSession] = useState<AnswerSession>(initialSession);
  const [storyRecord, setStoryRecord] = useState<AnswerStoryRecord | null>(null);
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const submitTranscript = useCallback(
    async (transcript: string) => {
      setError(null);
      setIsSubmitting(true);

      try {
        const result = await submitVoiceResponse({
          sessionId: session.id,
          transcript,
        });

        // Update state with response
        setSession(result.session);
        setStoryRecord(result.storyRecord);
      } catch (err) {
        const message = err instanceof Error ? err.message : 'An unexpected error occurred';

        frontendLogger.error(
          'Failed to submit voice response',
          err instanceof Error ? err : new Error(String(err)),
          { module: 'useSessionDataLoader', action: 'submitTranscript' },
        );

        setError(message);
      } finally {
        setIsSubmitting(false);
      }
    },
    [session.id],
  );

  return {
    session,
    storyRecord,
    isSubmitting,
    error,
    submitTranscript,
  };
}
