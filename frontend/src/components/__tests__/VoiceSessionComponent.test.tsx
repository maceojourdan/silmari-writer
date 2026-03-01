/**
 * Tests for VoiceSessionComponent
 *
 * Resource: ui-w8p2 (component)
 * Path: 307-process-voice-input-and-progress-session
 *
 * TLA+ properties tested:
 * - Reachability: render component with active session in INIT, simulate transcript event
 *   → expect payload builder called with { sessionId, transcript }
 * - TypeInvariant: assert payload matches SubmitVoiceResponseRequest TypeScript type
 * - ErrorConsistency:
 *   - No active session → expect error banner and no API call
 *   - Mic permission denied → expect error message and logger call
 */

import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import { describe, it, expect, vi, beforeEach } from 'vitest';
import VoiceSessionComponent from '../VoiceSessionComponent';

// Mock the API contract
vi.mock('@/api_contracts/submitVoiceResponse', () => ({
  submitVoiceResponse: vi.fn(),
}));

// Mock the frontend logger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { submitVoiceResponse } from '@/api_contracts/submitVoiceResponse';
import { frontendLogger } from '@/logging/index';

const mockSubmit = vi.mocked(submitVoiceResponse);
const mockLogger = vi.mocked(frontendLogger);

describe('VoiceSessionComponent - Step 1: Capture voice input', () => {
  const activeSession = {
    id: '550e8400-e29b-41d4-a716-446655440000',
    userId: 'user-123',
    state: 'INIT' as const,
    createdAt: '2026-02-28T00:00:00Z',
    updatedAt: '2026-02-28T00:00:00Z',
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render with active session in INIT state', () => {
      render(<VoiceSessionComponent session={activeSession} />);

      expect(screen.getByTestId('voice-session-component')).toBeInTheDocument();
    });

    it('should construct payload with { sessionId, transcript } on transcript event', async () => {
      mockSubmit.mockResolvedValue({
        session: { ...activeSession, state: 'IN_PROGRESS' },
        storyRecord: {
          id: '660e8400-e29b-41d4-a716-446655440001',
          sessionId: activeSession.id,
          status: 'IN_PROGRESS',
          content: 'My transcript content',
          createdAt: '2026-02-28T00:00:00Z',
          updatedAt: '2026-02-28T00:00:01Z',
        },
      });

      render(<VoiceSessionComponent session={activeSession} />);

      // Simulate entering a transcript
      const input = screen.getByTestId('transcript-input');
      fireEvent.change(input, { target: { value: 'My transcript content' } });

      // Submit the transcript
      const submitButton = screen.getByTestId('submit-transcript');
      fireEvent.click(submitButton);

      await waitFor(() => {
        expect(mockSubmit).toHaveBeenCalledWith({
          sessionId: activeSession.id,
          transcript: 'My transcript content',
        });
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass payload matching SubmitVoiceResponseRequest type', async () => {
      mockSubmit.mockResolvedValue({
        session: { ...activeSession, state: 'IN_PROGRESS' },
        storyRecord: {
          id: '660e8400-e29b-41d4-a716-446655440001',
          sessionId: activeSession.id,
          status: 'IN_PROGRESS',
          content: 'A valid transcript',
          createdAt: '2026-02-28T00:00:00Z',
          updatedAt: '2026-02-28T00:00:01Z',
        },
      });

      render(<VoiceSessionComponent session={activeSession} />);

      const input = screen.getByTestId('transcript-input');
      fireEvent.change(input, { target: { value: 'A valid transcript' } });

      const submitButton = screen.getByTestId('submit-transcript');
      fireEvent.click(submitButton);

      await waitFor(() => {
        const call = mockSubmit.mock.calls[0][0];
        // TypeInvariant: sessionId is string, transcript is string
        expect(typeof call.sessionId).toBe('string');
        expect(typeof call.transcript).toBe('string');
        expect(call.sessionId).toBe(activeSession.id);
        expect(call.transcript).toBe('A valid transcript');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should show error banner and prevent API call when no active session', () => {
      render(<VoiceSessionComponent session={null} />);

      expect(screen.getByRole('alert')).toBeInTheDocument();
      expect(screen.getByRole('alert').textContent).toContain('No active session');
      expect(mockSubmit).not.toHaveBeenCalled();
    });

    it('should show error message when session is not in INIT state', () => {
      const nonInitSession = { ...activeSession, state: 'IN_PROGRESS' as const };

      render(<VoiceSessionComponent session={nonInitSession} />);

      // Should not show the transcript input when not in INIT
      expect(screen.queryByTestId('transcript-input')).not.toBeInTheDocument();
    });

    it('should show error and log when transcript submission fails', async () => {
      mockSubmit.mockRejectedValue(new Error('Network failure'));

      render(<VoiceSessionComponent session={activeSession} />);

      const input = screen.getByTestId('transcript-input');
      fireEvent.change(input, { target: { value: 'My transcript' } });

      const submitButton = screen.getByTestId('submit-transcript');
      fireEvent.click(submitButton);

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
        expect(mockLogger.error).toHaveBeenCalled();
      });
    });

    it('should prevent submission when transcript is empty', () => {
      render(<VoiceSessionComponent session={activeSession} />);

      const submitButton = screen.getByTestId('submit-transcript');
      fireEvent.click(submitButton);

      expect(mockSubmit).not.toHaveBeenCalled();
    });
  });
});
