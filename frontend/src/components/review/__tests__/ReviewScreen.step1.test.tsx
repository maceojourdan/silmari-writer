/**
 * ReviewScreen.step1.test.tsx - Step 1: Capture edit-by-voice action
 *
 * TLA+ Properties:
 * - Reachability: Render ReviewScreen → click "Edit by Voice" → voiceMode === 'capturing'
 * - TypeInvariant: Voice session object matches VoiceSession type { status, attempts }
 * - ErrorConsistency: initializeVoiceSession() throws → error banner with VOICE_INIT_FAILED.code → still on review screen
 *
 * Resource: ui-w8p2 (component)
 * Path: 332-voice-edit-no-input-error-on-review-screen
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

const mockFetch = vi.fn();

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

describe('ReviewScreen — Step 1: Capture edit-by-voice action (Path 332)', () => {
  const contentId = '550e8400-e29b-41d4-a716-446655440000';

  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
    vi.restoreAllMocks();
    vi.resetModules();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render ReviewScreen with voice edit button', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      expect(screen.getByTestId('review-screen')).toBeInTheDocument();
      expect(screen.getByRole('button', { name: /edit by voice/i })).toBeInTheDocument();
    });

    it('should transition to voice capturing mode when Edit by Voice clicked', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      await waitFor(() => {
        expect(screen.getByTestId('voice-capture-active')).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should expose voice session with status and attempts fields', async () => {
      const onVoiceSessionChange = vi.fn();
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(
        <ReviewScreen
          selectedContentId={contentId}
          onVoiceSessionChange={onVoiceSessionChange}
        />,
      );

      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      await waitFor(() => {
        expect(onVoiceSessionChange).toHaveBeenCalled();
      });

      const session = onVoiceSessionChange.mock.calls[0][0];
      expect(session).toHaveProperty('status');
      expect(session).toHaveProperty('attempts');
      expect(session.status).toBe('capturing');
      expect(typeof session.attempts).toBe('number');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display VOICE_INIT_FAILED error when voice initialization fails', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');

      // Render with a prop that forces initialization failure
      render(
        <ReviewScreen
          selectedContentId={contentId}
          __testForceVoiceInitError={true}
        />,
      );

      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('Unable to start voice capture');
      });
    });

    it('should remain on review screen when voice initialization fails', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');

      render(
        <ReviewScreen
          selectedContentId={contentId}
          __testForceVoiceInitError={true}
        />,
      );

      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // Should still be on review screen
      expect(screen.getByTestId('review-screen')).toBeInTheDocument();
    });
  });
});
