/**
 * StartVoiceSessionModule - Frontend module for initiating a voice-assisted
 * answer session. Wraps in RequireAuth and calls createSession API contract.
 *
 * Resource: ui-v3n6 (module)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Flow:
 *   1. RequireAuth ensures user is authenticated (redirects to /login if not)
 *   2. User clicks "Start Voice-Assisted Session"
 *   3. Calls createSession() API contract
 *   4. On success → navigates to /session/[id] with INIT state
 *   5. On failure → displays error message
 */

'use client';

import { useState, useCallback, createContext, useContext } from 'react';
import { RequireAuth, type AuthUser } from '@/access_controls/RequireAuth';
import { createSession } from '@/api_contracts/createSession';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type VoiceSessionState = 'idle' | 'loading' | 'success' | 'error';

export interface VoiceSessionContext {
  sessionId: string | null;
  state: 'INIT' | null;
}

export interface StartVoiceSessionModuleProps {
  user: AuthUser | null;
  authToken: string | null;
  onNavigate: (path: string) => void;
}

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

const SessionContext = createContext<VoiceSessionContext>({
  sessionId: null,
  state: null,
});

export function useVoiceSession(): VoiceSessionContext {
  return useContext(SessionContext);
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function StartVoiceSessionModule({
  user,
  authToken,
  onNavigate,
}: StartVoiceSessionModuleProps) {
  const [uiState, setUIState] = useState<VoiceSessionState>('idle');
  const [error, setError] = useState<string | null>(null);
  const [sessionContext, setSessionContext] = useState<VoiceSessionContext>({
    sessionId: null,
    state: null,
  });

  const handleUnauthenticated = useCallback(() => {
    onNavigate('/login');
  }, [onNavigate]);

  const handleStartSession = async () => {
    if (!authToken) {
      onNavigate('/login');
      return;
    }

    setUIState('loading');
    setError(null);

    try {
      const result = await createSession(authToken);

      const newContext: VoiceSessionContext = {
        sessionId: result.sessionId,
        state: result.state,
      };

      setSessionContext(newContext);
      setUIState('success');
      onNavigate(`/session/${result.sessionId}`);
    } catch (err) {
      const message = err instanceof Error ? err.message : 'An unexpected error occurred';
      frontendLogger.error(
        'VOICE_SESSION_START_FAILED',
        err instanceof Error ? err : new Error(String(err)),
        { module: 'StartVoiceSessionModule', action: 'handleStartSession' },
      );
      setError(message);
      setUIState('error');
    }
  };

  return (
    <RequireAuth user={user} onUnauthenticated={handleUnauthenticated}>
      <SessionContext.Provider value={sessionContext}>
        <div data-testid="start-voice-session-module">
          {uiState === 'idle' && (
            <button
              onClick={handleStartSession}
              aria-label="Start Voice-Assisted Session"
              className="px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
            >
              Start Voice-Assisted Session
            </button>
          )}

          {uiState === 'loading' && (
            <div data-testid="loading-indicator">
              <span className="text-sm">Creating session...</span>
            </div>
          )}

          {uiState === 'success' && (
            <div data-testid="session-init" className="text-green-600">
              <span>Session initialized: {sessionContext.state}</span>
            </div>
          )}

          {uiState === 'error' && (
            <div data-testid="session-error" role="alert" className="text-red-600">
              <span>{error || 'An unexpected error occurred'}</span>
            </div>
          )}
        </div>
      </SessionContext.Provider>
    </RequireAuth>
  );
}
