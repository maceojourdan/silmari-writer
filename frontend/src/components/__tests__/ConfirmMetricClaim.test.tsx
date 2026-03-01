/**
 * Tests for ConfirmMetricClaim
 *
 * Resource: ui-w8p2 (component)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * TLA+ properties tested:
 * - Reachability: Render with claimId + source → select Y → click submit → payload passed to API contract
 * - TypeInvariant: status is "confirmed" | "denied"; claim_id is string; source is string
 * - ErrorConsistency: No selection → verifier prevents API call → inline validation error rendered
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the confirmTruthCheck API contract
vi.mock('@/api_contracts/confirmTruthCheck', () => ({
  confirmTruthCheck: vi.fn(),
}));

import ConfirmMetricClaim from '../ConfirmMetricClaim';
import { confirmTruthCheck } from '@/api_contracts/confirmTruthCheck';

const mockConfirmTruthCheck = vi.mocked(confirmTruthCheck);

describe('ConfirmMetricClaim', () => {
  const validProps = {
    claimId: 'claim-001',
    source: 'Annual Revenue Report 2025',
  };

  beforeEach(() => {
    mockConfirmTruthCheck.mockReset();
  });

  describe('Reachability: Select Y → submit → API called with correct payload', () => {
    it('should render the component with Confirm and Deny buttons', () => {
      render(<ConfirmMetricClaim {...validProps} />);

      expect(screen.getByRole('button', { name: /confirm/i })).toBeInTheDocument();
      expect(screen.getByRole('button', { name: /deny/i })).toBeInTheDocument();
      expect(screen.getByRole('button', { name: /submit/i })).toBeInTheDocument();
    });

    it('should call confirmTruthCheck with confirmed payload when Y selected', async () => {
      mockConfirmTruthCheck.mockResolvedValueOnce({
        id: 'tc-001',
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
        created_at: '2026-02-28T12:00:00.000Z',
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(mockConfirmTruthCheck).toHaveBeenCalledTimes(1);
        expect(mockConfirmTruthCheck).toHaveBeenCalledWith({
          claim_id: 'claim-001',
          status: 'confirmed',
          source: 'Annual Revenue Report 2025',
        });
      });
    });

    it('should call confirmTruthCheck with denied payload when N selected', async () => {
      mockConfirmTruthCheck.mockResolvedValueOnce({
        id: 'tc-002',
        claim_id: 'claim-001',
        status: 'denied',
        source: 'Annual Revenue Report 2025',
        created_at: '2026-02-28T12:00:00.000Z',
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /deny/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(mockConfirmTruthCheck).toHaveBeenCalledWith({
          claim_id: 'claim-001',
          status: 'denied',
          source: 'Annual Revenue Report 2025',
        });
      });
    });
  });

  describe('TypeInvariant: Payload structure', () => {
    it('should send claim_id as string, status as confirmed/denied, source as string', async () => {
      mockConfirmTruthCheck.mockResolvedValueOnce({
        id: 'tc-001',
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
        created_at: '2026-02-28T12:00:00.000Z',
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        const calledWith = mockConfirmTruthCheck.mock.calls[0][0];
        expect(typeof calledWith.claim_id).toBe('string');
        expect(['confirmed', 'denied']).toContain(calledWith.status);
        expect(typeof calledWith.source).toBe('string');
      });
    });

    it('should map Y decision to confirmed status', async () => {
      mockConfirmTruthCheck.mockResolvedValueOnce({
        id: 'tc-001',
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
        created_at: '2026-02-28T12:00:00.000Z',
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(mockConfirmTruthCheck.mock.calls[0][0].status).toBe('confirmed');
      });
    });

    it('should map N decision to denied status', async () => {
      mockConfirmTruthCheck.mockResolvedValueOnce({
        id: 'tc-002',
        claim_id: 'claim-001',
        status: 'denied',
        source: 'Annual Revenue Report 2025',
        created_at: '2026-02-28T12:00:00.000Z',
      });

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /deny/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(mockConfirmTruthCheck.mock.calls[0][0].status).toBe('denied');
      });
    });
  });

  describe('ErrorConsistency: No selection → validation error', () => {
    it('should show validation error when no selection made', async () => {
      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByText(/selection/i)).toBeInTheDocument();
      });
      expect(mockConfirmTruthCheck).not.toHaveBeenCalled();
    });

    it('should display API error when confirmTruthCheck fails', async () => {
      mockConfirmTruthCheck.mockRejectedValueOnce(new Error('Server error'));

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByText(/server error/i)).toBeInTheDocument();
      });
    });

    it('should show loading state during API call', async () => {
      let resolvePromise: (value: unknown) => void;
      const pendingPromise = new Promise((resolve) => {
        resolvePromise = resolve;
      });
      mockConfirmTruthCheck.mockReturnValueOnce(pendingPromise as Promise<any>);

      render(<ConfirmMetricClaim {...validProps} />);

      await userEvent.click(screen.getByRole('button', { name: /confirm/i }));
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /submit/i })).toBeDisabled();
      });

      // Resolve to clean up
      resolvePromise!({
        id: 'tc-001',
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
        created_at: '2026-02-28T12:00:00.000Z',
      });
    });
  });
});
