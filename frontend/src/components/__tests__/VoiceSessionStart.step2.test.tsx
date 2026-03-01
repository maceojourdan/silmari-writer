/**
 * VoiceSessionStart.step2.test.tsx - Step 2: Capture Consent Response
 *
 * TLA+ Properties:
 * - Reachability: select "I agree" → expect consentFlag === true (API called)
 * - TypeInvariant: consentFlag is boolean
 * - ErrorConsistency:
 *   - Select "Decline" → assert blocked state message shown
 *   - Verify no API call when declined
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

describe('VoiceSessionStart — Step 2: Capture Consent Response', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call API with consent: true when user clicks "I agree"', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ sessionStatus: 'INIT' }),
      });

      render(<VoiceSessionStart />);
      await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /i agree/i })).toBeInTheDocument();
      });

      await userEvent.click(screen.getByRole('button', { name: /i agree/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe('/api/voice-session/start');
      const body = JSON.parse(options.body);
      expect(body.consent).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send consent as a boolean true in the API call', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ sessionStatus: 'INIT' }),
      });

      render(<VoiceSessionStart />);
      await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /i agree/i })).toBeInTheDocument();
      });

      await userEvent.click(screen.getByRole('button', { name: /i agree/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      expect(typeof body.consent).toBe('boolean');
      expect(body.consent).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should show blocked message when user clicks "Decline"', async () => {
      render(<VoiceSessionStart />);
      await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
      });

      await userEvent.click(screen.getByRole('button', { name: /decline/i }));

      await waitFor(() => {
        expect(screen.getByText(/affirmative consent is required/i)).toBeInTheDocument();
      });
    });

    it('should NOT call API when user declines', async () => {
      render(<VoiceSessionStart />);
      await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /decline/i })).toBeInTheDocument();
      });

      await userEvent.click(screen.getByRole('button', { name: /decline/i }));

      // Wait a bit then check
      await new Promise((r) => setTimeout(r, 100));
      expect(mockFetch).not.toHaveBeenCalled();
    });
  });
});
