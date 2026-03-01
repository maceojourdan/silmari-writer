'use client';

/**
 * VoiceSessionComponent - Captures voice input and submits it for session progression.
 *
 * Resource: ui-w8p2 (component)
 * Path: 307-process-voice-input-and-progress-session
 *
 * Flow:
 *   1. Receives active session in INIT state
 *   2. User enters/captures transcript
 *   3. On submit, constructs { sessionId, transcript } payload
 *   4. Calls submitVoiceResponse API contract
 *   5. Displays success or error state
 *
 * Guards:
 *   - No active session → error banner, no API call
 *   - Session not in INIT → read-only state
 *   - Empty transcript → prevent submission
 *   - Submission failure → error message + logger call
 */

import { useState } from 'react';
import type { AnswerSession } from '@/server/data_structures/AnswerSession';
import type { SubmitVoiceResponseResponse } from '@/api_contracts/submitVoiceResponse';
import { submitVoiceResponse } from '@/api_contracts/submitVoiceResponse';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Props
// ---------------------------------------------------------------------------

export interface VoiceSessionComponentProps {
  session: AnswerSession | null;
  onSessionProgressed?: (result: SubmitVoiceResponseResponse) => void;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function VoiceSessionComponent({
  session,
  onSessionProgressed,
}: VoiceSessionComponentProps) {
  const [transcript, setTranscript] = useState('');
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [error, setError] = useState<string | null>(null);

  // Guard: No active session
  if (!session) {
    return (
      <div data-testid="voice-session-component">
        <div className="text-sm text-red-600" role="alert">
          No active session found. Please start a session first.
        </div>
      </div>
    );
  }

  // Guard: Session not in INIT state — show read-only
  if (session.state !== 'INIT') {
    return (
      <div data-testid="voice-session-component">
        <div className="text-sm text-gray-500">
          Session is in {session.state} state. Voice input is only available in INIT state.
        </div>
      </div>
    );
  }

  const handleSubmit = async () => {
    // Guard: Empty transcript
    if (!transcript.trim()) {
      return;
    }

    setError(null);
    setIsSubmitting(true);

    try {
      const result = await submitVoiceResponse({
        sessionId: session.id,
        transcript: transcript.trim(),
      });

      // Success — notify parent
      onSessionProgressed?.(result);
    } catch (err) {
      const message = err instanceof Error ? err.message : 'An unexpected error occurred';
      frontendLogger.error(
        'Voice response submission failed',
        err instanceof Error ? err : new Error(String(err)),
        { component: 'VoiceSessionComponent', action: 'handleSubmit' },
      );
      setError(message);
    } finally {
      setIsSubmitting(false);
    }
  };

  return (
    <div data-testid="voice-session-component" className="flex flex-col gap-3">
      <textarea
        data-testid="transcript-input"
        className="w-full p-3 border border-border rounded-md text-sm resize-none"
        placeholder="Enter your response..."
        value={transcript}
        onChange={(e) => setTranscript(e.target.value)}
        disabled={isSubmitting}
        rows={4}
      />

      <button
        data-testid="submit-transcript"
        type="button"
        className="px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50"
        onClick={handleSubmit}
        disabled={isSubmitting || !transcript.trim()}
      >
        {isSubmitting ? 'Submitting...' : 'Submit Response'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
