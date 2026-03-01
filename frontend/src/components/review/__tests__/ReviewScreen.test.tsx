/**
 * ReviewScreen.test.tsx - Step 1: Capture approve action in UI
 *
 * TLA+ Properties:
 * - Reachability: Render with selectedContentId="c1" → click Approve → API contract called with { contentId: "c1" }
 * - TypeInvariant: approveContent is called with { contentId: string }; component state transitions to submitting: boolean
 * - ErrorConsistency: Render with no selectedContentId → click Approve → validation message rendered; API NOT called
 *
 * Resource: ui-w8p2 (component)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock fetch at the network level
const mockFetch = vi.fn();

import ReviewScreen from '../ReviewScreen';

describe('ReviewScreen — Step 1: Capture Approve Action', () => {
  const contentId = '550e8400-e29b-41d4-a716-446655440000';

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
    it('should call API with { contentId } when content is selected and Approve clicked', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          entity: {
            id: contentId,
            status: 'APPROVED',
            workflowStage: 'FINALIZE',
            createdAt: '2026-02-28T12:00:00.000Z',
            updatedAt: '2026-02-28T12:01:00.000Z',
          },
          workflowStage: 'FINALIZE',
        }),
      });

      render(<ReviewScreen selectedContentId={contentId} />);
      await userEvent.click(screen.getByRole('button', { name: /approve/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe('/api/review/approve');
      expect(options.method).toBe('POST');

      const body = JSON.parse(options.body);
      expect(body.contentId).toBe(contentId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload with contentId as string', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          entity: {
            id: contentId,
            status: 'APPROVED',
            workflowStage: 'FINALIZE',
            createdAt: '2026-02-28T12:00:00.000Z',
            updatedAt: '2026-02-28T12:01:00.000Z',
          },
          workflowStage: 'FINALIZE',
        }),
      });

      render(<ReviewScreen selectedContentId={contentId} />);
      await userEvent.click(screen.getByRole('button', { name: /approve/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      expect(typeof body.contentId).toBe('string');
      expect(body.contentId).toBe(contentId);
    });

    it('should transition to submitting state when approve is clicked', async () => {
      // Create a promise that we control
      let resolveResponse: (value: unknown) => void;
      const responsePromise = new Promise((resolve) => {
        resolveResponse = resolve;
      });

      mockFetch.mockReturnValueOnce(responsePromise);

      render(<ReviewScreen selectedContentId={contentId} />);
      await userEvent.click(screen.getByRole('button', { name: /approve/i }));

      // Button should be in submitting state
      await waitFor(() => {
        const button = screen.getByRole('button', { name: /approving/i });
        expect(button).toBeDisabled();
      });

      // Resolve the response
      resolveResponse!({
        ok: true,
        json: async () => ({
          entity: {
            id: contentId,
            status: 'APPROVED',
            workflowStage: 'FINALIZE',
            createdAt: '2026-02-28T12:00:00.000Z',
            updatedAt: '2026-02-28T12:01:00.000Z',
          },
          workflowStage: 'FINALIZE',
        }),
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should render validation message when no content is selected', async () => {
      render(<ReviewScreen />);
      await userEvent.click(screen.getByRole('button', { name: /approve/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should NOT call API when no content is selected', async () => {
      render(<ReviewScreen />);
      await userEvent.click(screen.getByRole('button', { name: /approve/i }));

      expect(mockFetch).not.toHaveBeenCalled();
    });

    it('should render validation message with empty string content ID', async () => {
      render(<ReviewScreen selectedContentId="" />);
      await userEvent.click(screen.getByRole('button', { name: /approve/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });

      expect(mockFetch).not.toHaveBeenCalled();
    });
  });
});
