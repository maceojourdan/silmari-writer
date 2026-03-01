/**
 * FinalizeSessionButton.ui.test.tsx - Step 6: Display finalized session state in UI
 *
 * TLA+ Properties:
 * - Reachability: Mock successful API → click → confirmation text visible
 * - TypeInvariant: Component state matches { sessionState: "FINALIZE", storyRecordStatus: "FINALIZED" }
 * - ErrorConsistency: Mock API rejection → logger called → retry prompt rendered → backend not re-called
 *
 * Resource: ui-w8p2 (component)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock fetch at the network level
const mockFetch = vi.fn();

// Mock the frontend logger
vi.mock('../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { frontendLogger } from '../../logging/index';
import FinalizeSessionButton from '../FinalizeSessionButton';

const mockLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const successResponse = {
  sessionState: 'FINALIZE',
  storyRecordStatus: 'FINALIZED',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeSessionButton — Step 6: Display finalized session state in UI', () => {
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
    it('should call API with POST to finalize endpoint when clicked', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      render(<FinalizeSessionButton sessionId={sessionId} sessionState="ACTIVE" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe(`/api/sessions/${sessionId}/finalize`);
      expect(options.method).toBe('POST');
    });

    it('should display confirmation text on success', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      render(<FinalizeSessionButton sessionId={sessionId} sessionState="ACTIVE" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        expect(screen.getByText(/session finalized/i)).toBeInTheDocument();
      });
    });

    it('should display StoryRecord status on success', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      render(<FinalizeSessionButton sessionId={sessionId} sessionState="ACTIVE" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        expect(screen.getByText(/FINALIZED/)).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should reflect sessionState FINALIZE and storyRecordStatus FINALIZED in UI', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      render(<FinalizeSessionButton sessionId={sessionId} sessionState="ACTIVE" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        const successElement = screen.getByTestId('finalize-success');
        expect(successElement).toBeInTheDocument();
        expect(successElement.textContent).toContain('FINALIZE');
        expect(successElement.textContent).toContain('FINALIZED');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should block API call when session state is not ACTIVE', async () => {
      render(<FinalizeSessionButton sessionId={sessionId} sessionState="DRAFT" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      expect(mockFetch).not.toHaveBeenCalled();
    });

    it('should render error message when session state is not ACTIVE', async () => {
      render(<FinalizeSessionButton sessionId={sessionId} sessionState="DRAFT" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('ACTIVE');
      });
    });

    it('should call frontendLogger.error on API rejection', async () => {
      mockFetch.mockRejectedValueOnce(new TypeError('Failed to fetch'));

      render(<FinalizeSessionButton sessionId={sessionId} sessionState="ACTIVE" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        expect(mockLogger.error).toHaveBeenCalled();
      });
    });

    it('should render retry prompt on API failure', async () => {
      mockFetch.mockRejectedValueOnce(new TypeError('Failed to fetch'));

      render(<FinalizeSessionButton sessionId={sessionId} sessionState="ACTIVE" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /retry/i })).toBeInTheDocument();
      });
    });

    it('should not re-call backend automatically on failure', async () => {
      mockFetch.mockRejectedValueOnce(new TypeError('Failed to fetch'));

      render(<FinalizeSessionButton sessionId={sessionId} sessionState="ACTIVE" />);
      await userEvent.click(screen.getByRole('button', { name: /finalize session/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /retry/i })).toBeInTheDocument();
      });

      // Should only have been called once (no automatic retry)
      expect(mockFetch).toHaveBeenCalledTimes(1);
    });
  });
});
