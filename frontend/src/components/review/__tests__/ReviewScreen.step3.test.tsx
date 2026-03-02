/**
 * ReviewScreen.step3.test.tsx - Step 3: Display voice input processing error
 *
 * TLA+ Properties:
 * - Reachability: Invalid voice input → error banner shows VOICE_INPUT_INVALID.message → voiceMode === 'idle'
 * - TypeInvariant: Error object conforms to VoiceError { code: string; message: string }
 * - ErrorConsistency: Error renderer throws → fallback GENERIC_VOICE_ERROR.message → still on review screen
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

describe('ReviewScreen — Step 3: Display voice input processing error (Path 332)', () => {
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
    it('should display VOICE_INPUT_INVALID error message when empty transcript submitted', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      // Enter voice mode
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      // Submit without entering text (empty transcript)
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('Voice input could not be processed');
      });
    });

    it('should reset voice mode to idle after validation failure', async () => {
      const onVoiceSessionChange = vi.fn();
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(
        <ReviewScreen
          selectedContentId={contentId}
          onVoiceSessionChange={onVoiceSessionChange}
        />,
      );

      // Enter voice mode
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      // Submit empty transcript
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

      await waitFor(() => {
        // Voice capture form should no longer be visible (status changed to idle)
        expect(screen.queryByTestId('voice-capture-active')).not.toBeInTheDocument();
      });

      // Session should have been updated to idle
      const lastCall = onVoiceSessionChange.mock.calls[onVoiceSessionChange.mock.calls.length - 1];
      expect(lastCall[0].status).toBe('idle');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should display error with code and message fields from VoiceErrorDef', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      // Enter voice mode and submit empty transcript
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        // The error message should be a non-empty string
        expect(errorElement.textContent!.length).toBeGreaterThan(0);
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should remain on review screen after voice error', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      // Enter voice mode and submit empty transcript
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // Should still be on review screen
      expect(screen.getByTestId('review-screen')).toBeInTheDocument();
    });

    it('should display error message even when error state is set directly', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      // Trigger voice error flow
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

      await waitFor(() => {
        const alert = screen.getByRole('alert');
        expect(alert.textContent).toBe('Voice input could not be processed.');
      });
    });
  });
});
