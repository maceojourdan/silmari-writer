/**
 * voice-edit-no-input.integration.test.tsx - Integration test for Path 332
 *
 * Terminal Condition:
 *   User sees an error message indicating the voice input could not be processed,
 *   and the review screen remains visible with the original generated content unchanged.
 *
 * Feedback Loop:
 *   User may reattempt voice input up to 3 consecutive times from the same review session;
 *   after 3 failed attempts, the same error message is shown and no additional automatic retries occur.
 *
 * Resource: ui-w8p2 (component), ui-v3n6 (module), ui-a4y1 (verifier), cfg-j9w2 (errors)
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

describe('Path 332 Integration: Voice edit no-input error on review screen', () => {
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
  // Terminal Condition
  // -------------------------------------------------------------------------

  describe('Terminal Condition', () => {
    it('should complete the full voice-edit-no-input error flow end-to-end', async () => {
      const onVoiceSessionChange = vi.fn();
      const { default: ReviewScreen } = await import('../ReviewScreen');

      render(
        <ReviewScreen
          selectedContentId={contentId}
          onVoiceSessionChange={onVoiceSessionChange}
        />,
      );

      // 1. Render review screen with content
      expect(screen.getByTestId('review-screen')).toBeInTheDocument();

      // 2. Click "Edit by Voice"
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      // 3. Voice capture mode should be active
      expect(screen.getByTestId('voice-capture-active')).toBeInTheDocument();

      // 4. Submit with empty transcript (provide empty transcript)
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

      // 5. Error message displayed: "Voice input could not be processed."
      await waitFor(() => {
        const error = screen.getByRole('alert');
        expect(error.textContent).toBe('Voice input could not be processed.');
      });

      // 6. Review screen remains visible
      expect(screen.getByTestId('review-screen')).toBeInTheDocument();

      // 7. Attempt counter increments
      const lastSession = onVoiceSessionChange.mock.calls[onVoiceSessionChange.mock.calls.length - 1][0];
      expect(lastSession.attempts).toBe(1);
    });

    it('should not call any backend API during the error flow', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');

      render(<ReviewScreen selectedContentId={contentId} />);

      // Enter voice mode and submit empty
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // No backend calls should have been made
      expect(mockFetch).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // Feedback Loops: 3 consecutive failures
  // -------------------------------------------------------------------------

  describe('Feedback Loop: 3 consecutive failures', () => {
    it('should allow 3 consecutive failed attempts with same error', async () => {
      const onVoiceSessionChange = vi.fn();
      const { default: ReviewScreen } = await import('../ReviewScreen');

      render(
        <ReviewScreen
          selectedContentId={contentId}
          onVoiceSessionChange={onVoiceSessionChange}
        />,
      );

      // Attempt 1
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));
      await waitFor(() => {
        expect(screen.getByRole('alert').textContent).toBe('Voice input could not be processed.');
      });

      // Attempt 2
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));
      await waitFor(() => {
        expect(screen.getByRole('alert').textContent).toBe('Voice input could not be processed.');
      });

      // Attempt 3
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));
      await waitFor(() => {
        expect(screen.getByRole('alert').textContent).toBe('Voice input could not be processed.');
      });

      // Assert attempts === 3
      const allSessions = onVoiceSessionChange.mock.calls.map((c) => c[0]);
      const lastSession = allSessions[allSessions.length - 1];
      expect(lastSession.attempts).toBe(3);
    });

    it('should show same error message on all 3 attempts', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      const expectedMessage = 'Voice input could not be processed.';

      for (let i = 0; i < 3; i++) {
        await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
        await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

        await waitFor(() => {
          expect(screen.getByRole('alert').textContent).toBe(expectedMessage);
        });
      }
    });

    it('should not trigger automatic retries', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      // Do 3 manual attempts
      for (let i = 0; i < 3; i++) {
        await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
        await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

        await waitFor(() => {
          expect(screen.getByRole('alert')).toBeInTheDocument();
        });
      }

      // No automatic actions should have occurred - no fetch calls
      expect(mockFetch).not.toHaveBeenCalled();

      // Review screen should still be visible
      expect(screen.getByTestId('review-screen')).toBeInTheDocument();
    });

    it('should preserve review screen state through all 3 failures', async () => {
      const { default: ReviewScreen } = await import('../ReviewScreen');
      render(<ReviewScreen selectedContentId={contentId} />);

      for (let i = 0; i < 3; i++) {
        await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
        await userEvent.click(screen.getByRole('button', { name: /submit voice input/i }));

        await waitFor(() => {
          expect(screen.getByRole('alert')).toBeInTheDocument();
        });

        // Review screen is always visible
        expect(screen.getByTestId('review-screen')).toBeInTheDocument();

        // Approve and Return to Recall buttons should still be present
        expect(screen.getByRole('button', { name: /approve/i })).toBeInTheDocument();
        expect(screen.getByTestId('return-to-recall')).toBeInTheDocument();
      }
    });
  });
});
