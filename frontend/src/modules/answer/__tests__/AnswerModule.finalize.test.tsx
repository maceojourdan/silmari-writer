/**
 * AnswerModule.finalize.test.tsx - Step 5: Update UI to Locked State
 *
 * TLA+ Properties:
 * - Reachability: Mock API success → assert editing controls removed/disabled and status label "Finalized" visible
 * - TypeInvariant: Local state updated to { finalized: true, editable: false }
 * - ErrorConsistency: Mock API error → assert shared error shown and controls remain enabled
 *
 * Resource: ui-v3n6 (module)
 * Path: 333-finalize-answer-locks-editing
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor, act } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock fetch at the network level
const mockFetch = vi.fn();

import AnswerModule from '../AnswerModule';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

describe('AnswerModule — Step 5: Update UI to Locked State', () => {
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
    it('should show "Finalized" status and disable editing after successful finalization', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: answerId,
          finalized: true,
          editable: false,
        }),
      });

      render(
        <AnswerModule
          answerId={answerId}
          initialAnswer={{
            id: answerId,
            status: 'COMPLETED',
            finalized: false,
            editable: true,
            content: 'My answer content',
          }}
        />,
      );

      // Editing controls should be visible before finalization
      expect(screen.getByTestId('editing-controls')).toBeInTheDocument();

      // Click finalize
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(screen.getByText('Finalized')).toBeInTheDocument();
      });

      // Editing controls should be removed after finalization
      expect(screen.queryByTestId('editing-controls')).not.toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should update local state to { finalized: true, editable: false }', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: answerId,
          finalized: true,
          editable: false,
        }),
      });

      render(
        <AnswerModule
          answerId={answerId}
          initialAnswer={{
            id: answerId,
            status: 'COMPLETED',
            finalized: false,
            editable: true,
            content: 'My answer content',
          }}
        />,
      );

      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(screen.getByTestId('answer-status')).toHaveTextContent('Finalized');
      });

      // The finalize button should no longer be present
      expect(screen.queryByRole('button', { name: /finalize answer/i })).not.toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should show error message and keep controls enabled on API failure', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({
          code: 'INTERNAL_ERROR',
          message: 'Server error occurred',
        }),
      });

      render(
        <AnswerModule
          answerId={answerId}
          initialAnswer={{
            id: answerId,
            status: 'COMPLETED',
            finalized: false,
            editable: true,
            content: 'My answer content',
          }}
        />,
      );

      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });

      // Editing controls should remain visible
      expect(screen.getByTestId('editing-controls')).toBeInTheDocument();
    });
  });
});
