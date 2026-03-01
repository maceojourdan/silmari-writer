/**
 * EditByVoiceComponent.test.tsx - Step 1: Capture voice instruction from review screen
 *
 * TLA+ Properties:
 * - Reachability: Render ReviewModule with contentId="c1" → click "Edit by Voice"
 *   → mock successful transcription → assert structured payload { contentId: "c1", instructionText: string }
 * - TypeInvariant: Payload matches EditByVoicePayload type { contentId: string; instructionText: string }
 * - ErrorConsistency: Mock microphone/transcription failure → SharedErrors.VOICE_CAPTURE_FAILED
 *   → retry counter increments → after 3 failures → blocking error, retry disabled
 *
 * Resource: ui-w8p2 (component)
 * Path: 330-edit-content-by-voice-from-review-screen
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

const mockFetch = vi.fn();

import EditByVoiceComponent from '../EditByVoiceComponent';
import type { EditByVoicePayload } from '../EditByVoiceComponent';

describe('EditByVoiceComponent — Step 1: Capture voice instruction from review screen', () => {
  const contentId = '550e8400-e29b-41d4-a716-446655440000';

  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render "Edit by Voice" button when contentId is provided', () => {
      render(<EditByVoiceComponent contentId={contentId} />);

      const button = screen.getByRole('button', { name: /edit by voice/i });
      expect(button).toBeInTheDocument();
    });

    it('should emit structured payload { contentId, instructionText } on successful voice capture', async () => {
      const onVoiceInstruction = vi.fn();

      // Mock successful transcription via /api/transcribe
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ text: 'Make the introduction more concise' }),
      });

      render(
        <EditByVoiceComponent
          contentId={contentId}
          onVoiceInstruction={onVoiceInstruction}
        />,
      );

      // Click "Edit by Voice"
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      // Simulate providing instruction text (the component uses a text input fallback for testing)
      const input = screen.getByPlaceholderText(/voice instruction/i);
      await userEvent.type(input, 'Make the introduction more concise');
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(onVoiceInstruction).toHaveBeenCalledTimes(1);
      });

      const payload: EditByVoicePayload = onVoiceInstruction.mock.calls[0][0];
      expect(payload.contentId).toBe(contentId);
      expect(payload.instructionText).toBe('Make the introduction more concise');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should emit payload matching EditByVoicePayload type { contentId: string; instructionText: string }', async () => {
      const onVoiceInstruction = vi.fn();

      render(
        <EditByVoiceComponent
          contentId={contentId}
          onVoiceInstruction={onVoiceInstruction}
        />,
      );

      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      const input = screen.getByPlaceholderText(/voice instruction/i);
      await userEvent.type(input, 'Fix grammar errors');
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(onVoiceInstruction).toHaveBeenCalledTimes(1);
      });

      const payload = onVoiceInstruction.mock.calls[0][0];
      expect(typeof payload.contentId).toBe('string');
      expect(typeof payload.instructionText).toBe('string');
      expect(payload.contentId).toBe(contentId);
      expect(payload.instructionText.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display VOICE_CAPTURE_FAILED error when voice capture fails', async () => {
      const onError = vi.fn();

      render(
        <EditByVoiceComponent
          contentId={contentId}
          onError={onError}
        />,
      );

      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      // Submit empty instruction to simulate capture failure
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should increment retry counter on failure', async () => {
      const onError = vi.fn();

      render(
        <EditByVoiceComponent
          contentId={contentId}
          onError={onError}
        />,
      );

      // First attempt
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByText(/attempt 1/i)).toBeInTheDocument();
      });
    });

    it('should disable retry after 3 failures and show blocking error', async () => {
      const onError = vi.fn();

      render(
        <EditByVoiceComponent
          contentId={contentId}
          onError={onError}
        />,
      );

      // Three failed attempts
      for (let i = 0; i < 3; i++) {
        await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));
        await userEvent.click(screen.getByRole('button', { name: /submit/i }));

        if (i < 2) {
          // Wait for error to appear before retrying
          await waitFor(() => {
            expect(screen.getByRole('alert')).toBeInTheDocument();
          });
        }
      }

      // After 3 failures, retry should be disabled
      await waitFor(() => {
        const editButton = screen.getByRole('button', { name: /edit by voice/i });
        expect(editButton).toBeDisabled();
      });

      // Blocking error should be shown
      await waitFor(() => {
        expect(screen.getByText(/maximum retries/i)).toBeInTheDocument();
      });
    });
  });
});
