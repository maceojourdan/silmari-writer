/**
 * ConversationVoiceModule.step6.test.tsx - Step 6: Render transcript in UI
 *
 * TLA+ Properties:
 * - Reachability: simulate receiving TRANSCRIPT_FINAL event → transcript rendered in DOM
 * - TypeInvariant: transcript passes TranscriptVerifier before state update
 * - ErrorConsistency:
 *     - invalid transcript payload → verifier rejects, frontend logger called, fallback error rendered
 *
 * Resource: ui-v3n6 (module)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, act } from '@testing-library/react';
import { ConversationVoiceModule } from '../ConversationVoiceModule';

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { frontendLogger } from '@/logging/index';

const mockLogger = vi.mocked(frontendLogger);

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

describe('ConversationVoiceModule — Step 6: Render transcript in UI', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render transcript text when receiving valid TRANSCRIPT_FINAL event', () => {
      const onEvent = vi.fn();

      const { container } = render(
        <ConversationVoiceModule
          sessionId={validSessionId}
          onEventHandler={(handler) => { onEvent.mockImplementation(handler); }}
        />,
      );

      // Simulate receiving a TRANSCRIPT_FINAL event
      act(() => {
        onEvent({
          type: 'TRANSCRIPT_FINAL',
          text: 'Hello world transcript',
          sessionId: validSessionId,
        });
      });

      expect(screen.getByText('Hello world transcript')).toBeInTheDocument();
    });

    it('should render multiple transcripts in order', () => {
      const onEvent = vi.fn();

      render(
        <ConversationVoiceModule
          sessionId={validSessionId}
          onEventHandler={(handler) => { onEvent.mockImplementation(handler); }}
        />,
      );

      act(() => {
        onEvent({
          type: 'TRANSCRIPT_FINAL',
          text: 'First message',
          sessionId: validSessionId,
        });
      });

      act(() => {
        onEvent({
          type: 'TRANSCRIPT_FINAL',
          text: 'Second message',
          sessionId: validSessionId,
        });
      });

      expect(screen.getByText('First message')).toBeInTheDocument();
      expect(screen.getByText('Second message')).toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate transcript through TranscriptVerifier before rendering', () => {
      const onEvent = vi.fn();

      render(
        <ConversationVoiceModule
          sessionId={validSessionId}
          onEventHandler={(handler) => { onEvent.mockImplementation(handler); }}
        />,
      );

      // Valid event should render
      act(() => {
        onEvent({
          type: 'TRANSCRIPT_FINAL',
          text: 'Validated transcript',
          sessionId: validSessionId,
        });
      });

      expect(screen.getByText('Validated transcript')).toBeInTheDocument();
      // No error logged for valid transcript
      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should render fallback error when transcript payload is invalid', () => {
      const onEvent = vi.fn();

      render(
        <ConversationVoiceModule
          sessionId={validSessionId}
          onEventHandler={(handler) => { onEvent.mockImplementation(handler); }}
        />,
      );

      // Send invalid payload (missing text)
      act(() => {
        onEvent({
          type: 'TRANSCRIPT_FINAL',
          text: '',
          sessionId: validSessionId,
        });
      });

      expect(screen.getByText(/unable to display transcript/i)).toBeInTheDocument();
    });

    it('should log error when transcript validation fails', () => {
      const onEvent = vi.fn();

      render(
        <ConversationVoiceModule
          sessionId={validSessionId}
          onEventHandler={(handler) => { onEvent.mockImplementation(handler); }}
        />,
      );

      act(() => {
        onEvent({
          type: 'TRANSCRIPT_FINAL',
          text: '',
          sessionId: validSessionId,
        });
      });

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('TRANSCRIPT_VALIDATION_FAILED'),
        expect.any(Error),
        expect.objectContaining({ module: 'ConversationVoiceModule' }),
      );
    });

    it('should render fallback for null payload', () => {
      const onEvent = vi.fn();

      render(
        <ConversationVoiceModule
          sessionId={validSessionId}
          onEventHandler={(handler) => { onEvent.mockImplementation(handler); }}
        />,
      );

      act(() => {
        onEvent(null);
      });

      expect(screen.getByText(/unable to display transcript/i)).toBeInTheDocument();
    });
  });
});
