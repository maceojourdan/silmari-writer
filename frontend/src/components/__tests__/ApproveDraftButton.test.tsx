/**
 * Tests for ApproveDraftButton
 *
 * Resource: ui-w8p2 (component)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * TLA+ properties tested:
 * - Reachability: Render with valid IDs → click → approveStory() called
 * - TypeInvariant: Payload matches Zod schema from approveStory.ts
 * - ErrorConsistency: Missing draftId → verifier error shown, no API call
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the approveStory API contract
vi.mock('@/api_contracts/approveStory', () => ({
  approveStory: vi.fn(),
}));

// Mock next/navigation
vi.mock('next/navigation', () => ({
  useRouter: () => ({
    push: vi.fn(),
  }),
}));

import ApproveDraftButton from '../ApproveDraftButton';
import { approveStory } from '@/api_contracts/approveStory';

const mockApproveStory = vi.mocked(approveStory);

describe('ApproveDraftButton', () => {
  const validProps = {
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
  };

  beforeEach(() => {
    mockApproveStory.mockReset();
  });

  describe('Reachability: Click triggers API call', () => {
    it('should render the Approve Draft button', () => {
      render(<ApproveDraftButton {...validProps} />);
      expect(screen.getByRole('button', { name: /approve draft/i })).toBeInTheDocument();
    });

    it('should call approveStory with payload on click', async () => {
      mockApproveStory.mockResolvedValueOnce({
        storyRecordId: 'story-001',
        status: 'FINALIZED',
        persistedAt: '2026-02-28T12:00:00.000Z',
      });

      render(<ApproveDraftButton {...validProps} />);
      const button = screen.getByRole('button', { name: /approve draft/i });

      await userEvent.click(button);

      await waitFor(() => {
        expect(mockApproveStory).toHaveBeenCalledTimes(1);
        expect(mockApproveStory).toHaveBeenCalledWith({
          draftId: 'draft-001',
          resumeId: 'resume-001',
          jobId: 'job-001',
          questionId: 'question-001',
          voiceSessionId: 'session-001',
        });
      });
    });
  });

  describe('TypeInvariant: Payload structure', () => {
    it('should send all required identifiers in the payload', async () => {
      mockApproveStory.mockResolvedValueOnce({
        storyRecordId: 'story-001',
        status: 'FINALIZED',
        persistedAt: '2026-02-28T12:00:00.000Z',
      });

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        const calledWith = mockApproveStory.mock.calls[0][0];
        expect(calledWith).toHaveProperty('draftId');
        expect(calledWith).toHaveProperty('resumeId');
        expect(calledWith).toHaveProperty('jobId');
        expect(calledWith).toHaveProperty('questionId');
        expect(calledWith).toHaveProperty('voiceSessionId');
      });
    });
  });

  describe('ErrorConsistency: Validation blocks submission', () => {
    it('should show validation error and NOT call API when draftId is empty', async () => {
      render(<ApproveDraftButton {...validProps} draftId="" />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/draftId/i)).toBeInTheDocument();
      });
      expect(mockApproveStory).not.toHaveBeenCalled();
    });

    it('should show validation error when resumeId is empty', async () => {
      render(<ApproveDraftButton {...validProps} resumeId="" />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/resumeId/i)).toBeInTheDocument();
      });
      expect(mockApproveStory).not.toHaveBeenCalled();
    });

    it('should display API error when approveStory fails', async () => {
      mockApproveStory.mockRejectedValueOnce(new Error('Server error'));

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/server error/i)).toBeInTheDocument();
      });
    });

    it('should show loading state during API call', async () => {
      // Create a promise that we control
      let resolvePromise: (value: unknown) => void;
      const pendingPromise = new Promise((resolve) => {
        resolvePromise = resolve;
      });
      mockApproveStory.mockReturnValueOnce(pendingPromise as Promise<any>);

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /approve draft/i })).toBeDisabled();
      });

      // Resolve to clean up
      resolvePromise!({
        storyRecordId: 'story-001',
        status: 'FINALIZED',
        persistedAt: '2026-02-28T12:00:00.000Z',
      });
    });

    it('should show confirmation on success', async () => {
      mockApproveStory.mockResolvedValueOnce({
        storyRecordId: 'story-001',
        status: 'FINALIZED',
        persistedAt: '2026-02-28T12:00:00.000Z',
      });

      render(<ApproveDraftButton {...validProps} />);
      await userEvent.click(screen.getByRole('button', { name: /approve draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/approved/i)).toBeInTheDocument();
      });
    });
  });
});
