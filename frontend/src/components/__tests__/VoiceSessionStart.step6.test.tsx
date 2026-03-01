/**
 * VoiceSessionStart.step6.test.tsx - Step 6: Render Final User State
 *
 * TLA+ Properties:
 * - Reachability: mock success → voice session active UI rendered
 * - TypeInvariant: response parsed via typed contract
 * - ErrorConsistency:
 *   - Mock CONSENT_REQUIRED → session inactive + visible message
 *   - Mock malformed response → log + fallback error notification
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
import { frontendLogger } from '../../logging/index';

const mockLogger = vi.mocked(frontendLogger);

describe('VoiceSessionStart — Step 6: Render Final User State', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // Helper: navigate through to consent prompt and agree
  async function navigateToAgreement() {
    render(<VoiceSessionStart />);
    await userEvent.click(screen.getByRole('button', { name: /start voice session/i }));
    await waitFor(() => {
      expect(screen.getByRole('button', { name: /i agree/i })).toBeInTheDocument();
    });
    await userEvent.click(screen.getByRole('button', { name: /i agree/i }));
  }

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render active session UI on successful backend response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ sessionStatus: 'INIT' }),
      });

      await navigateToAgreement();

      await waitFor(() => {
        expect(screen.getByTestId('voice-session-active')).toBeInTheDocument();
      });
    });

    it('should display session status as active', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ sessionStatus: 'INIT' }),
      });

      await navigateToAgreement();

      await waitFor(() => {
        expect(screen.getByText(/session active/i)).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should show consent-required message on CONSENT_REQUIRED error', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 400,
        json: () =>
          Promise.resolve({
            code: 'CONSENT_REQUIRED',
            message: 'Affirmative consent is required before starting voice session',
          }),
      });

      await navigateToAgreement();

      await waitFor(() => {
        expect(screen.getByText(/affirmative consent is required/i)).toBeInTheDocument();
      });
    });

    it('should show fallback error on malformed response and log via frontendLogger', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ garbage: true }),
      });

      await navigateToAgreement();

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should show error on network failure and log via frontendLogger', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      await navigateToAgreement();

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      expect(mockLogger.error).toHaveBeenCalled();
    });
  });
});
