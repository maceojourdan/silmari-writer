/**
 * VoiceSessionStart.feedback.test.tsx - Feedback Loop (Max 3 Attempts)
 *
 * TLA+ Properties:
 * - Provide 3 non-affirmative responses
 * - Assert session reset to initial state
 * - Assert further progression blocked until restart
 *
 * Resource: ui-w8p2 (component)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the frontend logger
vi.mock('../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock fetch at the network level
const mockFetch = vi.fn();

import VoiceSessionStart from '../VoiceSessionStart';

describe('VoiceSessionStart — Feedback Loop (Max 3 Attempts)', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  it('should allow retry after first decline', async () => {
    render(<VoiceSessionStart />);

    // Attempt 1: Start → Decline
    await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /decline/i }));

    // Should show retry option
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /try again/i })).toBeInTheDocument();
    });
  });

  it('should allow retry after second decline', async () => {
    render(<VoiceSessionStart />);

    // Attempt 1: Start → Decline
    await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /decline/i }));

    // Retry → Attempt 2: Decline again
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /try again/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /try again/i }));

    await waitFor(() => {
      expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /decline/i }));

    // Should still show retry option
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /try again/i })).toBeInTheDocument();
    });
  });

  it('should reset to idle state after 3 declined attempts', async () => {
    render(<VoiceSessionStart />);

    // Attempt 1: Start → Decline
    await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /decline/i }));

    // Attempt 2: Try again → Decline
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /try again/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /try again/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /decline/i }));

    // Attempt 3: Try again → Decline
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /try again/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /try again/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /decline/i }));

    // After 3 declines, should reset to idle with "Start Voice Session" button
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /start voice session/i })).toBeInTheDocument();
    });
  });

  it('should NOT make any API calls during decline flow', async () => {
    render(<VoiceSessionStart />);

    // 3 decline cycles
    for (let i = 0; i < 3; i++) {
      if (i === 0) {
        await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));
      } else {
        await waitFor(() => {
          expect(screen.getByRole('button', { name: /try again/i })).toBeInTheDocument();
        });
        await userEvent.click(screen.getByRole('button', { name: /try again/i }));
      }

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
      });
      await userEvent.click(screen.getByRole('button', { name: /decline/i }));
    }

    expect(mockFetch).not.toHaveBeenCalled();
  });

  it('should succeed if user agrees on second attempt', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ sessionStatus: 'INIT' }),
    });

    render(<VoiceSessionStart />);

    // Attempt 1: Start → Decline
    await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /decline/i }));

    // Attempt 2: Try again → Agree
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /try again/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /try again/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /i agree/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /i agree/i }));

    // Should show active session
    await waitFor(() => {
      expect(screen.getByTestId('voice-session-active')).toBeInTheDocument();
    });

    expect(mockFetch).toHaveBeenCalledTimes(1);
  });
});
