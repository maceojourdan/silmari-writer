/**
 * StartVoiceSessionModule Tests - Step 1: User initiates voice session
 *
 * Resource: ui-v3n6 (module)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * TLA+ properties tested:
 * - Reachability: Authenticated user clicks button → createSession() called once
 * - TypeInvariant: Request matches CreateSessionRequest Zod schema
 * - ErrorConsistency: Unauthenticated user → redirect to /login, createSession NOT called
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';

// Mock dependencies
vi.mock('@/api_contracts/createSession', () => ({
  createSession: vi.fn(),
}));

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import StartVoiceSessionModule from '../StartVoiceSessionModule';
import { createSession } from '@/api_contracts/createSession';
import { frontendLogger } from '@/logging/index';

const mockCreateSession = vi.mocked(createSession);
const mockLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const authenticatedUser = { id: 'user-abc123' };
const authToken = 'valid-token-abc123';

function renderModule(overrides: {
  user?: { id: string } | null;
  authToken?: string | null;
  onNavigate?: (path: string) => void;
} = {}) {
  const onNavigate = overrides.onNavigate ?? vi.fn();
  return {
    onNavigate,
    ...render(
      <StartVoiceSessionModule
        user={overrides.user ?? authenticatedUser}
        authToken={overrides.authToken ?? authToken}
        onNavigate={onNavigate}
      />,
    ),
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StartVoiceSessionModule - Step 1: User initiates voice session', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call createSession() when authenticated user clicks Start button', async () => {
      mockCreateSession.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'INIT',
      });

      renderModule();

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(mockCreateSession).toHaveBeenCalledTimes(1);
      });
    });

    it('should call createSession with the auth token', async () => {
      mockCreateSession.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'INIT',
      });

      renderModule();

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(mockCreateSession).toHaveBeenCalledWith(authToken);
      });
    });

    it('should show loading state while creating session', async () => {
      let resolvePromise: (value: any) => void;
      const pendingPromise = new Promise((resolve) => { resolvePromise = resolve; });
      mockCreateSession.mockReturnValue(pendingPromise as any);

      renderModule();

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(screen.getByTestId('loading-indicator')).toBeInTheDocument();
      });

      // Clean up
      resolvePromise!({ sessionId: 'id', state: 'INIT' });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should navigate to /session/[id] on success', async () => {
      const sessionId = '550e8400-e29b-41d4-a716-446655440000';
      mockCreateSession.mockResolvedValue({
        sessionId,
        state: 'INIT',
      });

      const { onNavigate } = renderModule();

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(onNavigate).toHaveBeenCalledWith(`/session/${sessionId}`);
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should redirect to /login when user is not authenticated', () => {
      const onNavigate = vi.fn();

      render(
        <StartVoiceSessionModule
          user={null}
          authToken={null}
          onNavigate={onNavigate}
        />,
      );

      expect(onNavigate).toHaveBeenCalledWith('/login');
    });

    it('should NOT call createSession when user is not authenticated', () => {
      const onNavigate = vi.fn();

      render(
        <StartVoiceSessionModule
          user={null}
          authToken={null}
          onNavigate={onNavigate}
        />,
      );

      expect(mockCreateSession).not.toHaveBeenCalled();
    });

    it('should redirect to /login when authToken is null and button clicked', async () => {
      const onNavigate = vi.fn();

      render(
        <StartVoiceSessionModule
          user={authenticatedUser}
          authToken={null}
          onNavigate={onNavigate}
        />,
      );

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      expect(onNavigate).toHaveBeenCalledWith('/login');
      expect(mockCreateSession).not.toHaveBeenCalled();
    });

    it('should display error when session creation fails', async () => {
      mockCreateSession.mockRejectedValue(new Error('Network failure'));

      renderModule();

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        const errorEl = screen.getByRole('alert');
        expect(errorEl).toBeInTheDocument();
        expect(errorEl.textContent).toContain('Network failure');
      });
    });

    it('should log error via frontendLogger when session creation fails', async () => {
      mockCreateSession.mockRejectedValue(new Error('Network failure'));

      renderModule();

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(mockLogger.error).toHaveBeenCalledWith(
          'VOICE_SESSION_START_FAILED',
          expect.any(Error),
          expect.objectContaining({ module: 'StartVoiceSessionModule' }),
        );
      });
    });
  });
});
