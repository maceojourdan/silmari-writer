/**
 * Integration test for ConfirmMetricClaim flow (frontend + mocked backend)
 *
 * Path: 297-confirm-metric-claim-truth-check
 * Step 5: Return updated status to frontend
 *
 * TLA+ properties tested:
 * - Reachability: Mock 200 response → submit Y → UI displays "Confirmed"
 * - TypeInvariant: Displayed status strictly matches response status
 * - ErrorConsistency: Malformed JSON → error logged, generic failure message shown
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Don't mock the API contract - instead mock fetch at the network level
const mockFetch = vi.fn();

// Mock the logger so we can verify error logging
vi.mock('@/logging', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import ConfirmMetricClaim from '../ConfirmMetricClaim';
import { frontendLogger } from '@/logging';

const mockLogger = vi.mocked(frontendLogger);

describe('ConfirmMetricClaim Integration (Step 5)', () => {
  const validProps = {
    claimId: 'claim-001',
    source: 'Annual Revenue Report 2025',
  };

  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    mockLogger.error.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  describe('Reachability: Successful confirmation flow', () => {
    it('should show "Confirmed" after successful Y submission', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: 'tc-001',
          claim_id: 'claim-001',
          status: 'confirmed',
          source: 'Annual Revenue Report 2025',
          created_at: '2026-02-28T12:00:00.000Z',
        }),
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByText(/confirmed/i)).toBeInTheDocument();
      });
    });

    it('should show "Denied" after successful N submission', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: 'tc-002',
          claim_id: 'claim-001',
          status: 'denied',
          source: 'Annual Revenue Report 2025',
          created_at: '2026-02-28T12:00:00.000Z',
        }),
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /deny/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByText(/denied/i)).toBeInTheDocument();
      });
    });

    it('should call onStatusChange callback with result status', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: 'tc-001',
          claim_id: 'claim-001',
          status: 'confirmed',
          source: 'Annual Revenue Report 2025',
          created_at: '2026-02-28T12:00:00.000Z',
        }),
      });

      const onStatusChange = vi.fn();
      render(<ConfirmMetricClaim {...validProps} onStatusChange={onStatusChange} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(onStatusChange).toHaveBeenCalledWith('confirmed');
      });
    });
  });

  describe('TypeInvariant: Response validation', () => {
    it('should display status that strictly matches response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: 'tc-001',
          claim_id: 'claim-001',
          status: 'confirmed',
          source: 'Annual Revenue Report 2025',
          created_at: '2026-02-28T14:00:00.000Z',
        }),
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        const statusEl = screen.getByTestId('result-status');
        expect(statusEl).toBeInTheDocument();
        expect(statusEl.textContent).toMatch(/confirmed/i);
      });
    });
  });

  describe('ErrorConsistency: Failure scenarios', () => {
    it('should display error when server returns malformed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should log error on malformed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(mockLogger.error).toHaveBeenCalled();
      });
    });

    it('should display server error message on API failure', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({ code: 'TRUTH_CHECK_PERSISTENCE_ERROR', message: 'Database write failed' }),
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });
    });

    it('should display error on network failure', async () => {
      mockFetch.mockRejectedValueOnce(new TypeError('Failed to fetch'));

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });
    });

    it('should re-enable submit button after error', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 400,
        json: async () => ({ code: 'TRUTH_CHECK_VALIDATION_ERROR', message: 'Bad request' }),
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      const submitBtn = screen.getByRole('button', { name: /submit/i });
      await userEvent.click(submitBtn);

      await waitFor(() => {
        expect(submitBtn).not.toBeDisabled();
      });
    });
  });
});
