/**
 * DraftSessionView.test.tsx - Step 6: Return Updated Session to UI
 *
 * TLA+ Properties:
 * - Reachability: Mock API returns { state: 'FINALIZE' } → click Approve → UI shows FINALIZE + confirmation
 * - TypeInvariant: Response matches Session schema
 * - ErrorConsistency: Malformed response → generic error displayed → state unchanged
 *
 * Resource: ui-v3n6 (module)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock fetch at the network level
const mockFetch = vi.fn();

import DraftSessionView from '../DraftSessionView';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const draftSession = {
  id: sessionId,
  state: 'DRAFT',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const finalizeResponse = {
  id: sessionId,
  state: 'FINALIZE',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftSessionView — Step 6: Return Updated Session to UI', () => {
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
    it('should display FINALIZE status label after successful approval', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => finalizeResponse,
      });

      render(<DraftSessionView session={draftSession} />);

      // Initial state should show DRAFT
      expect(screen.getByTestId('session-status').textContent).toBe('DRAFT');

      // Click approve
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      // Wait for status to update
      await waitFor(() => {
        expect(screen.getByTestId('session-status').textContent).toBe('FINALIZE');
      });
    });

    it('should show confirmation message after successful approval', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => finalizeResponse,
      });

      render(<DraftSessionView session={draftSession} />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      await waitFor(() => {
        expect(screen.getByTestId('approval-confirmation')).toBeInTheDocument();
        expect(screen.getByTestId('approval-confirmation').textContent).toContain('FINALIZE');
      });
    });

    it('should hide approve button after successful approval', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => finalizeResponse,
      });

      render(<DraftSessionView session={draftSession} />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      // Wait for the success state
      await waitFor(() => {
        expect(screen.getByTestId('approval-confirmation')).toBeInTheDocument();
      });

      // The approve button in the parent should be gone (replaced by success state)
      // since session.state is now FINALIZE, the conditional rendering hides ApproveButton
      expect(screen.queryByRole('button', { name: /approve session/i })).not.toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate response conforms to Session schema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => finalizeResponse,
      });

      render(<DraftSessionView session={draftSession} />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      // Valid response should result in status update
      await waitFor(() => {
        expect(screen.getByTestId('session-status').textContent).toBe('FINALIZE');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display generic error on malformed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      render(<DraftSessionView session={draftSession} />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should keep session state as DRAFT when response is malformed', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      render(<DraftSessionView session={draftSession} />);
      await userEvent.click(screen.getByRole('button', { name: /approve session/i }));

      // Wait for error to appear
      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // State should remain DRAFT
      expect(screen.getByTestId('session-status').textContent).toBe('DRAFT');
    });
  });
});
