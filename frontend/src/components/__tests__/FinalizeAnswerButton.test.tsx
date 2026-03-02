/**
 * FinalizeAnswerButton.test.tsx - Step 1: Capture Finalize Action
 *
 * TLA+ Properties:
 * - Reachability: Render component with { editable: true, answerId }, click button → assert finalizeAnswer(answerId) called
 * - TypeInvariant: Assert contract call matches Zod schema { answerId: string }
 * - ErrorConsistency: Render with { editable: false }, click → assert no API call and shared error message displayed from SharedErrors.ANSWER_ALREADY_FINALIZED
 *
 * Resource: ui-w8p2 (component)
 * Path: 333-finalize-answer-locks-editing
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { FinalizeAnswerRequestSchema } from '@/api_contracts/finalizeAnswer';

// Mock fetch at the network level
const mockFetch = vi.fn();

import FinalizeAnswerButton from '../FinalizeAnswerButton';

describe('FinalizeAnswerButton — Step 1: Capture Finalize Action', () => {
  const answerId = '550e8400-e29b-41d4-a716-446655440000';

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
    it('should call API with answerId when editable is true', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: answerId,
          finalized: true,
          editable: false,
        }),
      });

      render(<FinalizeAnswerButton answerId={answerId} editable={true} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe(`/api/answers/${answerId}/finalize`);
      expect(options.method).toBe('POST');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload that satisfies FinalizeAnswerRequestSchema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: answerId,
          finalized: true,
          editable: false,
        }),
      });

      render(<FinalizeAnswerButton answerId={answerId} editable={true} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = FinalizeAnswerRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should block API call when editable is false', async () => {
      render(<FinalizeAnswerButton answerId={answerId} editable={false} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      // API should NOT have been called
      expect(mockFetch).not.toHaveBeenCalled();
    });

    it('should render shared error message when editable is false', async () => {
      render(<FinalizeAnswerButton answerId={answerId} editable={false} />);
      await userEvent.click(screen.getByRole('button', { name: /finalize answer/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('already been finalized');
      });
    });

    it('should mark button as aria-disabled when editable is false', () => {
      render(<FinalizeAnswerButton answerId={answerId} editable={false} />);
      const button = screen.getByRole('button', { name: /finalize answer/i });
      expect(button).toHaveAttribute('aria-disabled', 'true');
    });
  });
});
