/**
 * Tests for StorySelection - Step 3: Block confirmation on misalignment
 *
 * Path: 314-prevent-confirmation-of-misaligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Misaligned result → confirmation callback NOT called, error message visible
 * - TypeInvariant: Component state contains errorMessage (string|null), isBlocked (boolean)
 * - ErrorConsistency (mapping fails): Unknown messageKey → fallback to STORY_MISALIGNED message
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock AlignmentVerifier
vi.mock('@/verifiers/AlignmentVerifier', () => ({
  AlignmentVerifier: {
    validate: vi.fn(),
  },
}));

// Mock fetch
const mockFetch = vi.fn();

import { StorySelection } from '../StorySelection';
import { AlignmentVerifier } from '@/verifiers/AlignmentVerifier';
import { AlignmentErrors } from '@/server/error_definitions/AlignmentErrors';
import type { Story } from '@/server/data_structures/ConfirmStory';

const mockValidate = vi.mocked(AlignmentVerifier.validate);

const testStories: Story[] = [
  {
    id: 'story-001',
    title: 'Led migration to microservices architecture',
    summary: 'Coordinated 4 teams to decompose a monolithic application.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
  {
    id: 'story-002',
    title: 'Built real-time analytics pipeline',
    summary: 'Designed streaming data pipeline processing 1M events per second.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
];

describe('StorySelection - Step 3: Block confirmation on misalignment', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    mockValidate.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should NOT call onConfirmed when alignment validation returns misaligned', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'STORY_MISALIGNED',
      });

      const onConfirmed = vi.fn();

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={onConfirmed}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      // Wait for alignment validation to complete
      await waitFor(() => {
        expect(mockValidate).toHaveBeenCalledTimes(1);
      });

      // Confirmation callback should NOT have been called
      expect(onConfirmed).not.toHaveBeenCalled();

      // API should NOT have been called
      expect(mockFetch).not.toHaveBeenCalled();
    });

    it('should display an error message when alignment validation fails', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'STORY_MISALIGNED',
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByText(AlignmentErrors.STORY_MISALIGNED)).toBeInTheDocument();
      });
    });

    it('should call onConfirmed when alignment validation returns aligned', async () => {
      mockValidate.mockReturnValue({ status: 'aligned' });

      const confirmedStory = { ...testStories[0], status: 'CONFIRMED' };
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          confirmedStoryId: 'story-001',
          status: 'CONFIRMED',
          story: confirmedStory,
          excludedCount: 1,
        }),
      });

      const onConfirmed = vi.fn();

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={onConfirmed}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(onConfirmed).toHaveBeenCalled();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should show alignment error as a string message', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'ALIGNMENT_RULES_UNAVAILABLE',
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        const errorElement = screen.getByTestId('alignment-error');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toBeTruthy();
        expect(typeof errorElement.textContent).toBe('string');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency (mapping fails)
  // -------------------------------------------------------------------------

  describe('ErrorConsistency (mapping fails)', () => {
    it('should fall back to STORY_MISALIGNED message when messageKey is unknown', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'TOTALLY_UNKNOWN_KEY',
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByText(AlignmentErrors.STORY_MISALIGNED)).toBeInTheDocument();
      });
    });

    it('should fall back to STORY_MISALIGNED message when messageKey is undefined', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        // No messageKey provided
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByText(AlignmentErrors.STORY_MISALIGNED)).toBeInTheDocument();
      });
    });

    it('should clear alignment error when user selects a different story', async () => {
      mockValidate
        .mockReturnValueOnce({ status: 'misaligned', messageKey: 'STORY_MISALIGNED' })
        .mockReturnValueOnce({ status: 'aligned' });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      // First select and get misaligned
      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByText(AlignmentErrors.STORY_MISALIGNED)).toBeInTheDocument();
      });

      // Select a different story - error should clear
      await userEvent.click(screen.getByLabelText('Built real-time analytics pipeline'));

      expect(screen.queryByTestId('alignment-error')).not.toBeInTheDocument();
    });
  });
});
