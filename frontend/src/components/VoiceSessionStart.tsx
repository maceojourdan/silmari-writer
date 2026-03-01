'use client';

/**
 * VoiceSessionStart - Captures user intent to start voice session,
 * enforces affirmative consent before proceeding.
 *
 * Resource: ui-w8p2 (component)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * UI States: idle → consent_prompt → (blocked | loading | active | error)
 *
 * Flow:
 *   1. Click "Start Voice Session" → show consent prompt
 *   2. User selects "I agree" or "Decline"
 *   3. On agree → call API with consent: true → render active session
 *   4. On decline → show blocked message with retry
 *   5. After 3 declines → reset to idle
 */

import { useState } from 'react';
import { isExplicitlyAffirmative } from '@/verifiers/consentVerifier';
import { startVoiceSession } from '@/api_contracts/startVoiceSession';
import { frontendLogger } from '@/logging/index';

type UIState = 'idle' | 'consent_prompt' | 'blocked' | 'loading' | 'active' | 'error';

const MAX_ATTEMPTS = 3;

export default function VoiceSessionStart() {
  const [uiState, setUIState] = useState<UIState>('idle');
  const [attemptCount, setAttemptCount] = useState(0);
  const [error, setError] = useState<string | null>(null);

  const handleStartClick = () => {
    setError(null);
    setUIState('consent_prompt');
  };

  const handleAgree = async () => {
    const consentFlag = isExplicitlyAffirmative('I agree');

    if (!consentFlag) {
      frontendLogger.error(
        'Consent verifier unexpectedly returned false for "I agree"',
        new Error('Verifier failure'),
        { component: 'VoiceSessionStart', action: 'handleAgree' },
      );
      setError('An unexpected error occurred');
      setUIState('error');
      return;
    }

    setUIState('loading');

    try {
      const result = await startVoiceSession({ consent: true });

      if (result.sessionStatus === 'INIT') {
        setUIState('active');
      }
    } catch (err) {
      const message = err instanceof Error ? err.message : 'An unexpected error occurred';
      frontendLogger.error(
        'Failed to start voice session',
        err instanceof Error ? err : new Error(String(err)),
        { component: 'VoiceSessionStart', action: 'handleAgree' },
      );
      setError(message);
      setUIState('error');
    }
  };

  const handleDecline = () => {
    const newAttemptCount = attemptCount + 1;
    setAttemptCount(newAttemptCount);

    if (newAttemptCount >= MAX_ATTEMPTS) {
      // Reset to idle after 3 declined attempts
      setAttemptCount(0);
      setError(null);
      setUIState('idle');
      return;
    }

    setError('Affirmative consent is required before starting voice session');
    setUIState('blocked');
  };

  const handleTryAgain = () => {
    setError(null);
    setUIState('consent_prompt');
  };

  // -------------------------------------------------------------------------
  // Render States
  // -------------------------------------------------------------------------

  if (uiState === 'active') {
    return (
      <div className="flex items-center gap-2 text-green-600" data-testid="voice-session-active">
        <span>Voice session active</span>
      </div>
    );
  }

  if (uiState === 'consent_prompt') {
    return (
      <div className="flex flex-col gap-3">
        <p className="text-sm font-medium">
          Do you consent to starting a voice session?
        </p>
        <div className="flex gap-2">
          <button
            className="px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
            onClick={handleAgree}
            aria-label="I agree"
          >
            I agree
          </button>
          <button
            className="px-4 py-2 text-sm font-medium rounded-md border border-border hover:bg-accent transition-colors"
            onClick={handleDecline}
            aria-label="Decline"
          >
            Decline
          </button>
        </div>
      </div>
    );
  }

  if (uiState === 'loading') {
    return (
      <div className="flex items-center gap-2">
        <span className="text-sm">Starting voice session...</span>
      </div>
    );
  }

  if (uiState === 'blocked') {
    return (
      <div className="flex flex-col gap-2">
        {error && (
          <div className="text-sm text-red-600" role="alert">
            {error}
          </div>
        )}
        <button
          className="px-4 py-2 text-sm font-medium rounded-md border border-border hover:bg-accent transition-colors"
          onClick={handleTryAgain}
          aria-label="Try again"
        >
          Try again
        </button>
      </div>
    );
  }

  if (uiState === 'error') {
    return (
      <div className="flex flex-col gap-2">
        <div className="text-sm text-red-600" role="alert">
          {error || 'An unexpected error occurred'}
        </div>
      </div>
    );
  }

  // Idle state (default)
  return (
    <div className="flex flex-col gap-2">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
        onClick={handleStartClick}
        aria-label="Start Voice Session"
      >
        Start Voice Session
      </button>
    </div>
  );
}
