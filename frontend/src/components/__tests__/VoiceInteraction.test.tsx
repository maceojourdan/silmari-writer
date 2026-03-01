/**
 * VoiceInteraction.test.tsx - Step 6: Deliver next prompt to user
 *
 * TLA+ Properties:
 * - Reachability: Render component with nextStepPayload → expect prompt text visible
 * - TypeInvariant: Assert props conform to NextStepPayload type
 * - ErrorConsistency: Simulate audio playback failure → VoiceLogger.error() called; fallback text displayed
 *
 * Resource: ui-w8p2 (component)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import { render, screen, waitFor } from '@testing-library/react';
import { describe, it, expect, vi, beforeEach } from 'vitest';
import VoiceInteraction from '../VoiceInteraction';
import type { NextStepPayload } from '../VoiceInteraction';

// Mock the frontend voice logger
vi.mock('@/logging/voiceInteractionLogger', () => ({
  voiceInteractionLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { voiceInteractionLogger } from '@/logging/voiceInteractionLogger';

const mockLogger = vi.mocked(voiceInteractionLogger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

function createNextStepPayload(overrides: Partial<NextStepPayload> = {}): NextStepPayload {
  return {
    sessionId: 'a1b2c3d4-e5f6-7890-abcd-ef1234567890',
    nextState: 'VERIFY',
    promptText: 'Great! Now let\'s verify the details of your story. Does everything look correct?',
    recallLoopDisabled: true,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VoiceInteraction — Step 6: Deliver next prompt to user', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render component with next step prompt text visible', () => {
      const payload = createNextStepPayload();

      render(<VoiceInteraction payload={payload} />);

      expect(screen.getByTestId('voice-interaction')).toBeInTheDocument();
      expect(screen.getByText(/verify the details/i)).toBeInTheDocument();
    });

    it('should display the next state indicator', () => {
      const payload = createNextStepPayload();

      render(<VoiceInteraction payload={payload} />);

      expect(screen.getByTestId('next-state-indicator')).toBeInTheDocument();
      expect(screen.getByTestId('next-state-indicator').textContent).toContain('VERIFY');
    });

    it('should indicate recall loop is disabled', () => {
      const payload = createNextStepPayload({ recallLoopDisabled: true });

      render(<VoiceInteraction payload={payload} />);

      expect(screen.getByTestId('recall-loop-status')).toBeInTheDocument();
      expect(screen.getByTestId('recall-loop-status').textContent).toContain('complete');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should accept props conforming to NextStepPayload type', () => {
      const payload: NextStepPayload = {
        sessionId: 'a1b2c3d4-e5f6-7890-abcd-ef1234567890',
        nextState: 'VERIFY',
        promptText: 'Please verify your story.',
        recallLoopDisabled: true,
      };

      const { container } = render(<VoiceInteraction payload={payload} />);

      expect(container).toBeDefined();
    });

    it('should display promptText as string content', () => {
      const payload = createNextStepPayload({
        promptText: 'Exact prompt text to display',
      });

      render(<VoiceInteraction payload={payload} />);

      expect(screen.getByTestId('prompt-text').textContent).toBe('Exact prompt text to display');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display fallback text when audio playback fails', async () => {
      // Mock window.speechSynthesis to simulate failure
      const mockSpeak = vi.fn().mockImplementation(() => {
        throw new Error('Audio playback failed');
      });
      Object.defineProperty(window, 'speechSynthesis', {
        value: { speak: mockSpeak, cancel: vi.fn() },
        writable: true,
        configurable: true,
      });

      const payload = createNextStepPayload({
        promptText: 'Verify your story now.',
      });

      render(<VoiceInteraction payload={payload} />);

      await waitFor(() => {
        expect(screen.getByTestId('fallback-text')).toBeInTheDocument();
        expect(screen.getByTestId('fallback-text').textContent).toContain('Verify your story now.');
      });
    });

    it('should call VoiceLogger.error on audio failure', async () => {
      const mockSpeak = vi.fn().mockImplementation(() => {
        throw new Error('Speech synthesis unavailable');
      });
      Object.defineProperty(window, 'speechSynthesis', {
        value: { speak: mockSpeak, cancel: vi.fn() },
        writable: true,
        configurable: true,
      });

      const payload = createNextStepPayload();

      render(<VoiceInteraction payload={payload} />);

      await waitFor(() => {
        expect(mockLogger.error).toHaveBeenCalled();
      });
    });

    it('should still show prompt text even when audio fails', async () => {
      const mockSpeak = vi.fn().mockImplementation(() => {
        throw new Error('Audio playback failed');
      });
      Object.defineProperty(window, 'speechSynthesis', {
        value: { speak: mockSpeak, cancel: vi.fn() },
        writable: true,
        configurable: true,
      });

      const payload = createNextStepPayload({
        promptText: 'Confirm your story details.',
      });

      render(<VoiceInteraction payload={payload} />);

      await waitFor(() => {
        expect(screen.getByTestId('prompt-text')).toBeInTheDocument();
      });
    });
  });
});
