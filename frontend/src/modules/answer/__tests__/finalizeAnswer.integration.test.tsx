/**
 * Integration test for the finalize-answer-locks-editing flow.
 *
 * Path: 333-finalize-answer-locks-editing
 *
 * Exercises the full path:
 * 1. Render UI with completed, editable answer
 * 2. Click Finalize
 * 3. Assert:
 *    - HTTP request sent to correct endpoint
 *    - UI shows "Finalized" status
 *    - Editing controls are disabled/removed
 *
 * TLA+ properties:
 * - Reachability: Trigger → UI → API → Service → DB → UI (mocked at network level)
 * - TypeInvariant: Entity shape preserved across layers
 * - ErrorConsistency: No illegal state transitions occur
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock fetch at the network level — simulates full backend
const mockFetch = vi.fn();

import AnswerModule from '../AnswerModule';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const completedAnswer = {
  id: answerId,
  status: 'COMPLETED',
  finalized: false,
  editable: true,
  content: 'My completed answer about leadership experience.',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Finalize Answer Integration (Path 333)', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full successful path
  // -------------------------------------------------------------------------

  describe('Reachability: Full successful finalization flow', () => {
    it('should complete full path: UI → API → Backend (mocked) → UI update', async () => {
      // Simulate backend returning finalized answer
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: answerId,
          finalized: true,
          editable: false,
        }),
      });

      render(<AnswerModule answerId={answerId} initialAnswer={completedAnswer} />);

      // Pre-condition: editing controls visible, status is COMPLETED
      expect(screen.getByTestId('editing-controls')).toBeInTheDocument();
      expect(screen.getByTestId('answer-status')).toHaveTextContent('COMPLETED');

      // Action: click finalize
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      // Post-condition: verify API was called correctly
      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe(`/api/answers/${answerId}/finalize`);
      expect(options.method).toBe('POST');

      // Post-condition: UI updated to finalized state
      await waitFor(() => {
        expect(screen.getByText('Finalized')).toBeInTheDocument();
      });

      // Post-condition: editing controls removed
      expect(screen.queryByTestId('editing-controls')).not.toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Request payload shape
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Entity shape preserved across layers', () => {
    it('should send request with correct answerId in payload', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: answerId,
          finalized: true,
          editable: false,
        }),
      });

      render(<AnswerModule answerId={answerId} initialAnswer={completedAnswer} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      expect(body.answerId).toBe(answerId);
    });

    it('should handle response with correct finalized shape', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: answerId,
          finalized: true,
          editable: false,
        }),
      });

      render(<AnswerModule answerId={answerId} initialAnswer={completedAnswer} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(screen.getByTestId('answer-status')).toHaveTextContent('Finalized');
      });

      // Finalize button should no longer be present
      expect(screen.queryByRole('button', { name: /finalize answer/i })).not.toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: No illegal state transitions
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: No illegal state transitions', () => {
    it('should keep answer editable when backend returns error', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 422,
        json: async () => ({
          code: 'ANSWER_NOT_COMPLETED',
          message: 'Answer is not in COMPLETED status',
        }),
      });

      render(<AnswerModule answerId={answerId} initialAnswer={completedAnswer} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      // Error should be displayed
      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // Editing controls should remain
      expect(screen.getByTestId('editing-controls')).toBeInTheDocument();

      // Status should still be COMPLETED, not Finalized
      expect(screen.getByTestId('answer-status')).toHaveTextContent('COMPLETED');
    });

    it('should display error message on network failure', async () => {
      mockFetch.mockRejectedValueOnce(new TypeError('Failed to fetch'));

      render(<AnswerModule answerId={answerId} initialAnswer={completedAnswer} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // Answer should still be editable
      expect(screen.getByTestId('editing-controls')).toBeInTheDocument();
    });

    it('should show error when response has invalid shape', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      render(<AnswerModule answerId={answerId} initialAnswer={completedAnswer} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // Controls remain visible — no state transition happened
      expect(screen.getByTestId('editing-controls')).toBeInTheDocument();
    });
  });
});
