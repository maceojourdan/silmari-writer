/**
 * ApproveButton.test.tsx - Step 1: Capture Approve Action
 *
 * TLA+ Properties:
 * - Reachability: Render with DRAFT session → click Approve → API contract called with { sessionId, action: 'APPROVE' }
 * - TypeInvariant: Payload satisfies ApproveSessionRequestSchema
 * - ErrorConsistency: Render with FINALIZE state → click Approve → verifier blocks → validation message rendered
 *
 * Resource: ui-w8p2 (component)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { ApproveSessionRequestSchema } from '@/api_contracts/approveSession';

// Mock fetch at the network level
const mockFetch = vi.fn();

import ApproveButton from '../ApproveButton';

describe('ApproveButton — Step 1: Capture Approve Action', () => {
  const sessionId = '550e8400-e29b-41d4-a716-446655440000';

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
    it('should call API with { sessionId, action: APPROVE } when session is DRAFT', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: sessionId,
          state: 'FINALIZE',
          createdAt: '2026-02-28T12:00:00.000Z',
          updatedAt: '2026-02-28T12:01:00.000Z',
        }),
      });

      render(<ApproveButton sessionId={sessionId} sessionState="DRAFT" />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe(`/api/sessions/${sessionId}/approve`);
      expect(options.method).toBe('POST');

      const body = JSON.parse(options.body);
      expect(body.sessionId).toBe(sessionId);
      expect(body.action).toBe('APPROVE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload that satisfies ApproveSessionRequestSchema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: sessionId,
          state: 'FINALIZE',
          createdAt: '2026-02-28T12:00:00.000Z',
          updatedAt: '2026-02-28T12:01:00.000Z',
        }),
      });

      render(<ApproveButton sessionId={sessionId} sessionState="DRAFT" />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = ApproveSessionRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should block API call when session state is FINALIZE', async () => {
      render(<ApproveButton sessionId={sessionId} sessionState="FINALIZE" />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      // API should NOT have been called
      expect(mockFetch).not.toHaveBeenCalled();
    });

    it('should render validation message when session state is not DRAFT', async () => {
      render(<ApproveButton sessionId={sessionId} sessionState="FINALIZE" />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('FINALIZE');
      });
    });
  });
});
