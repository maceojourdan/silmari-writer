/**
 * Integration test for ApproveDraft flow (frontend + mocked backend)
 *
 * Path: 293-approve-voice-session-and-persist-story-record
 * Step 5: Return success response and update UI
 *
 * TLA+ properties tested:
 * - Reachability: Mock 200 response { storyRecordId } → click approve → confirmation shown
 * - TypeInvariant: Response conforms to ApproveStoryResponse schema
 * - ErrorConsistency: Malformed response → "Save failed. Please retry."
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock next/navigation
const mockPush = vi.fn();
vi.mock('next/navigation', () => ({
  useRouter: () => ({
    push: mockPush,
  }),
}));

// Don't mock the API contract - instead mock fetch at the network level
const mockFetch = vi.fn();

import ApproveDraftButton from '../ApproveDraftButton';

describe('ApproveDraft Integration (Step 5)', () => {
  const validProps = {
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
  };

  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    mockPush.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  describe('Reachability: Successful approval flow', () => {
    it('should show confirmation after successful API response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          storyRecordId: 'story-record-001',
          status: 'FINALIZED',
          persistedAt: '2026-02-28T12:00:00.000Z',
        }),
      });

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/approved/i)).toBeInTheDocument();
      });
    });

    it('should call onSuccess callback with storyRecordId', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          storyRecordId: 'story-record-001',
          status: 'FINALIZED',
          persistedAt: '2026-02-28T12:00:00.000Z',
        }),
      });

      const onSuccess = vi.fn();
      render(<ApproveDraftButton {...validProps} onSuccess={onSuccess} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(onSuccess).toHaveBeenCalledWith('story-record-001');
      });
    });
  });

  describe('TypeInvariant: Response validation', () => {
    it('should handle response with all required fields', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          storyRecordId: 'story-record-002',
          status: 'FINALIZED',
          persistedAt: '2026-02-28T14:00:00.000Z',
        }),
      });

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/approved/i)).toBeInTheDocument();
      });
    });
  });

  describe('ErrorConsistency: Failure scenarios', () => {
    it('should display error when server returns malformed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should display server error message on API failure', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({ code: 'PERSISTENCE_FAILED', message: 'Database write failed' }),
      });

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/database write failed/i)).toBeInTheDocument();
      });
    });

    it('should display generic error on network failure', async () => {
      mockFetch.mockRejectedValueOnce(new TypeError('Failed to fetch'));

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/failed to fetch/i)).toBeInTheDocument();
      });
    });

    it('should re-enable button after error', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      render(<ApproveDraftButton {...validProps} />);
      const button = screen.getByRole('button', { name: /approve draft/i });

      await userEvent.click(button);

      await waitFor(() => {
        expect(button).not.toBeDisabled();
      });
    });
  });
});
