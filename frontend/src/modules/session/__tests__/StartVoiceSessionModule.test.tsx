/**
 * StartVoiceSessionModule Tests - Step 1: User initiates voice session
 *
 * Resource: ui-v3n6 (module)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * TLA+ properties tested:
 * - Reachability: Authenticated user submits URL → startSessionFromUrl() called once
 * - TypeInvariant: Request matches StartSessionFromUrlRequest Zod schema
 * - ErrorConsistency: Unauthenticated user → redirect to /login, startSessionFromUrl NOT called
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor, act } from '@testing-library/react';

// Mock dependencies
vi.mock('@/api_contracts/startSessionFromUrl', async () => {
  const actual = await vi.importActual<typeof import('@/api_contracts/startSessionFromUrl')>(
    '@/api_contracts/startSessionFromUrl',
  );
  return {
    ...actual,
    startSessionFromUrl: vi.fn(),
  };
});

vi.mock('@/api_contracts/startSessionFromUpload', () => ({
  startSessionFromUpload: vi.fn(),
}));

vi.mock('@/api_contracts/startSessionDefaultQuestions', () => ({
  startSessionDefaultQuestions: vi.fn(),
}));

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import StartVoiceSessionModule, { type StartVoiceSessionModuleProps } from '../StartVoiceSessionModule';
import { StartSessionAlreadyActiveError, startSessionFromUrl } from '@/api_contracts/startSessionFromUrl';
import { startSessionFromUpload } from '@/api_contracts/startSessionFromUpload';
import { startSessionDefaultQuestions } from '@/api_contracts/startSessionDefaultQuestions';
import { frontendLogger } from '@/logging/index';

const mockStartSessionFromUrl = vi.mocked(startSessionFromUrl);
const mockStartSessionFromUpload = vi.mocked(startSessionFromUpload);
const mockStartSessionDefaultQuestions = vi.mocked(startSessionDefaultQuestions);
const mockLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const authenticatedUser = { id: 'user-abc123' };
const authToken = 'valid-token-abc123';
const sourceUrl = 'https://example.greenhouse.io/job/123';

function renderModule(overrides: {
  user?: { id: string } | null;
  authToken?: string | null;
  onNavigate?: StartVoiceSessionModuleProps['onNavigate'];
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
    it('renders and switches input modes (url, file_upload, default_questions)', () => {
      renderModule();

      expect(screen.getByTestId('input-mode-url')).toHaveAttribute('aria-pressed', 'true');
      expect(screen.getByLabelText(/job posting url/i)).toBeInTheDocument();

      fireEvent.click(screen.getByTestId('input-mode-file_upload'));

      expect(screen.getByTestId('input-mode-file_upload')).toHaveAttribute('aria-pressed', 'true');
      expect(screen.queryByLabelText(/job posting url/i)).not.toBeInTheDocument();
      expect(screen.getByTestId('input-mode-panel-file_upload')).toBeInTheDocument();

      fireEvent.click(screen.getByTestId('input-mode-default_questions'));

      expect(screen.getByTestId('input-mode-default_questions')).toHaveAttribute('aria-pressed', 'true');
      expect(screen.getByTestId('input-mode-panel-default_questions')).toBeInTheDocument();

      fireEvent.click(screen.getByTestId('input-mode-url'));

      expect(screen.getByTestId('input-mode-url')).toHaveAttribute('aria-pressed', 'true');
      expect(screen.getByLabelText(/job posting url/i)).toBeInTheDocument();
    });

    it('should call startSessionFromUrl() when authenticated user submits URL', async () => {
      mockStartSessionFromUrl.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'initialized',
        canonicalUrl: sourceUrl,
        contextSummary: 'Context extracted from example.greenhouse.io (direct URL).',
      });

      renderModule();

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(mockStartSessionFromUrl).toHaveBeenCalledTimes(1);
      });
    });

    it('should call startSessionFromUrl with auth token and URL', async () => {
      mockStartSessionFromUrl.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'initialized',
        canonicalUrl: sourceUrl,
        contextSummary: 'Context extracted from example.greenhouse.io (direct URL).',
      });

      renderModule();

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(mockStartSessionFromUrl).toHaveBeenCalledWith(authToken, sourceUrl);
      });
    });

    it('should show loading state while creating session', async () => {
      type SessionInitResult = Awaited<ReturnType<typeof startSessionFromUrl>>;
      const deferred = Promise.withResolvers<SessionInitResult>();
      mockStartSessionFromUrl.mockReturnValue(deferred.promise);

      renderModule();

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(screen.getByTestId('loading-indicator')).toBeInTheDocument();
      });

      // Clean up
      await act(async () => {
        deferred.resolve({
          sessionId: '550e8400-e29b-41d4-a716-446655440000',
          state: 'initialized',
          canonicalUrl: sourceUrl,
          contextSummary: 'Context extracted from example.greenhouse.io (direct URL).',
        });
      });
    });

    it('should call startSessionFromUpload when file_upload mode is selected', async () => {
      mockStartSessionFromUpload.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'initialized',
        inputMode: 'file_upload',
        questions: [
          {
            id: 'q-default-1',
            text: 'Tell us about your favourite project you worked on in recent memory and why you loved working on it so much.',
            category: 'default',
            position: 0,
          },
        ],
        questionProgress: {
          currentIndex: 0,
          total: 1,
          completed: [],
          activeQuestionId: 'q-default-1',
        },
      });

      renderModule();

      fireEvent.click(screen.getByTestId('input-mode-file_upload'));
      const fileInput = screen.getByTestId('file-upload-input');
      const resume = new File(['resume body'], 'resume.pdf', { type: 'application/pdf' });
      fireEvent.change(fileInput, {
        target: {
          files: [resume],
        },
      });

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(mockStartSessionFromUpload).toHaveBeenCalledWith(authToken, [resume]);
      });
    });

    it('should call startSessionDefaultQuestions when default mode is selected', async () => {
      mockStartSessionDefaultQuestions.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'initialized',
        inputMode: 'default_questions',
        questions: [
          {
            id: 'q-default-1',
            text: 'Tell us about your favourite project you worked on in recent memory and why you loved working on it so much.',
            category: 'default',
            position: 0,
          },
        ],
        questionProgress: {
          currentIndex: 0,
          total: 1,
          completed: [],
          activeQuestionId: 'q-default-1',
        },
      });

      renderModule();
      fireEvent.click(screen.getByTestId('input-mode-default_questions'));

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        expect(mockStartSessionDefaultQuestions).toHaveBeenCalledWith(authToken);
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should navigate to /session/[id] on success', async () => {
      const sessionId = '550e8400-e29b-41d4-a716-446655440000';
      mockStartSessionFromUrl.mockResolvedValue({
        sessionId,
        state: 'initialized',
        canonicalUrl: sourceUrl,
        contextSummary: 'Context extracted from example.greenhouse.io (direct URL).',
      });

      const { onNavigate } = renderModule();

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
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

    it('should NOT call startSessionFromUrl when user is not authenticated', () => {
      const onNavigate = vi.fn();

      render(
        <StartVoiceSessionModule
          user={null}
          authToken={null}
          onNavigate={onNavigate}
        />,
      );

      expect(mockStartSessionFromUrl).not.toHaveBeenCalled();
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

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      expect(onNavigate).toHaveBeenCalledWith('/login');
      expect(mockStartSessionFromUrl).not.toHaveBeenCalled();
    });

    it('should display error when session creation fails', async () => {
      mockStartSessionFromUrl.mockRejectedValue(new Error('Network failure'));

      renderModule();

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        const errorEl = screen.getByRole('alert');
        expect(errorEl).toBeInTheDocument();
        expect(errorEl.textContent).toContain('Network failure');
      });
    });

    it('shows actionable guidance when an active session conflict occurs', async () => {
      mockStartSessionFromUrl.mockRejectedValue(
        new StartSessionAlreadyActiveError('A session is already active.'),
      );

      renderModule();

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      await waitFor(() => {
        const errorEl = screen.getByRole('alert');
        expect(errorEl).toBeInTheDocument();
        expect(errorEl.textContent).toContain('already have an active session');
        expect(errorEl.textContent).toContain('finalize or end it');
      });
    });

    it('should log error via frontendLogger when session creation fails', async () => {
      mockStartSessionFromUrl.mockRejectedValue(new Error('Network failure'));

      renderModule();

      fireEvent.change(screen.getByLabelText(/job posting url/i), {
        target: { value: sourceUrl },
      });
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

    it('should require a URL before starting session', async () => {
      renderModule();

      const button = screen.getByRole('button', { name: /Start Voice-Assisted Session/i });
      fireEvent.click(button);

      expect(screen.getByRole('alert')).toHaveTextContent('Paste a job URL to continue.');
      expect(mockStartSessionFromUrl).not.toHaveBeenCalled();
    });
  });
});
