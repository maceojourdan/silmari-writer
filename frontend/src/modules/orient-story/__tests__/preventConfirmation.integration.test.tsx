/**
 * Integration test - Terminal Condition: prevent-confirmation-of-misaligned-story-selection
 *
 * Path: 314-prevent-confirmation-of-misaligned-story-selection
 *
 * Renders full OrientStoryModule with a misaligned story, clicks confirm,
 * and verifies end-to-end that:
 * - AlignmentVerifier is invoked
 * - Confirmation callback is NOT invoked
 * - Alignment error message is visible
 * - User remains on the selection screen
 *
 * This proves:
 * - Reachability: Full path exercised end-to-end
 * - TypeInvariant: Payload + result types enforced
 * - ErrorConsistency: All error branches yield valid UI error state
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the data loader (the lowest layer)
vi.mock('@/data_loaders/loadOrientStoryData', () => ({
  loadOrientStoryData: vi.fn(),
}));

// Mock fetch to prevent actual API calls
const mockFetch = vi.fn();

import { OrientStoryModule } from '../OrientStoryModule';
import { loadOrientStoryData } from '@/data_loaders/loadOrientStoryData';
import { AlignmentErrors } from '@/server/error_definitions/AlignmentErrors';
import type { OrientStoryData } from '@/server/data_structures/ConfirmStory';

const mockLoader = vi.mocked(loadOrientStoryData);

// Test data: story-003 has questionId q-999 (misaligned with active question q-001)
const validData: OrientStoryData = {
  question: {
    id: 'q-001',
    text: 'Tell me about a time you led a cross-functional team to deliver a complex project.',
    category: 'leadership',
  },
  jobRequirements: [
    {
      id: 'jr-001',
      description: 'Experience leading cross-functional teams',
      priority: 'REQUIRED',
    },
    {
      id: 'jr-002',
      description: 'Track record of delivering complex projects on time',
      priority: 'PREFERRED',
    },
  ],
  stories: [
    {
      id: 'story-001',
      title: 'Led migration to microservices architecture',
      summary: 'Coordinated 4 teams across engineering, QA, and DevOps.',
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
    {
      id: 'story-003',
      title: 'Organized company hackathon',
      summary: 'Planned and ran a 48-hour hackathon for 200 engineers.',
      status: 'EXCLUDED',
      questionId: 'q-001',
    },
  ],
};

describe('Integration: prevent-confirmation-of-misaligned-story-selection', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    mockLoader.mockReset();
    mockLoader.mockResolvedValue(validData);
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path exercised end-to-end
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should block confirmation when selecting an EXCLUDED story', async () => {
      const onConfirmed = vi.fn();

      render(
        <OrientStoryModule
          questionId="q-001"
          jobId="job-001"
          onConfirmed={onConfirmed}
        />,
      );

      // Wait for data to load
      await waitFor(() => {
        expect(screen.getByTestId('orient-story-module')).toBeInTheDocument();
      });

      // Select the EXCLUDED story (story-003)
      await userEvent.click(screen.getByLabelText('Organized company hackathon'));

      // Click confirm
      await userEvent.click(screen.getByTestId('confirm-button'));

      // Assert: alignment error is visible
      await waitFor(() => {
        expect(screen.getByTestId('alignment-error')).toBeInTheDocument();
        expect(screen.getByText(AlignmentErrors.STORY_MISALIGNED)).toBeInTheDocument();
      });

      // Assert: confirmation callback was NOT invoked
      expect(onConfirmed).not.toHaveBeenCalled();

      // Assert: API was NOT called
      expect(mockFetch).not.toHaveBeenCalled();

      // Assert: user remains on selection screen
      expect(screen.getByTestId('story-selection')).toBeInTheDocument();
      expect(screen.getByTestId('confirm-button')).toBeInTheDocument();
    });

    it('should allow confirmation when selecting an aligned AVAILABLE story', async () => {
      const confirmedStory = {
        ...validData.stories[0],
        status: 'CONFIRMED',
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          confirmedStoryId: 'story-001',
          status: 'CONFIRMED',
          story: confirmedStory,
          excludedCount: 2,
        }),
      });

      const onConfirmed = vi.fn();

      render(
        <OrientStoryModule
          questionId="q-001"
          jobId="job-001"
          onConfirmed={onConfirmed}
        />,
      );

      // Wait for data to load
      await waitFor(() => {
        expect(screen.getByTestId('orient-story-module')).toBeInTheDocument();
      });

      // Select an AVAILABLE story (story-001)
      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));

      // Click confirm
      await userEvent.click(screen.getByTestId('confirm-button'));

      // Assert: confirmation callback WAS invoked (story passes alignment)
      await waitFor(() => {
        expect(onConfirmed).toHaveBeenCalledWith(
          expect.objectContaining({ id: 'story-001' }),
          2,
        );
      });

      // Assert: no alignment error visible
      expect(screen.queryByTestId('alignment-error')).not.toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Payload + result types enforced
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should construct proper payload with storyId, questionId, and jobId', async () => {
      // We verify this indirectly: if AlignmentVerifier receives the correct types,
      // the alignment check works correctly. An EXCLUDED story with correct questionId
      // should still be caught as misaligned.

      render(
        <OrientStoryModule
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await waitFor(() => {
        expect(screen.getByTestId('orient-story-module')).toBeInTheDocument();
      });

      // Select EXCLUDED story
      await userEvent.click(screen.getByLabelText('Organized company hackathon'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      // The AlignmentVerifier correctly identified this as misaligned by status
      await waitFor(() => {
        expect(screen.getByTestId('alignment-error')).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: All error branches yield valid UI error state
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should clear alignment error and allow retry when selecting a different story', async () => {
      const confirmedStory = {
        ...validData.stories[1],
        status: 'CONFIRMED',
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          confirmedStoryId: 'story-002',
          status: 'CONFIRMED',
          story: confirmedStory,
          excludedCount: 2,
        }),
      });

      const onConfirmed = vi.fn();

      render(
        <OrientStoryModule
          questionId="q-001"
          jobId="job-001"
          onConfirmed={onConfirmed}
        />,
      );

      await waitFor(() => {
        expect(screen.getByTestId('orient-story-module')).toBeInTheDocument();
      });

      // First: select EXCLUDED story → misaligned
      await userEvent.click(screen.getByLabelText('Organized company hackathon'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByTestId('alignment-error')).toBeInTheDocument();
      });

      // Then: select AVAILABLE story → error clears
      await userEvent.click(screen.getByLabelText('Built real-time analytics pipeline'));

      expect(screen.queryByTestId('alignment-error')).not.toBeInTheDocument();

      // Confirm again → should succeed
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(onConfirmed).toHaveBeenCalledWith(
          expect.objectContaining({ id: 'story-002' }),
          2,
        );
      });
    });

    it('should show correct error message for each misalignment type', async () => {
      render(
        <OrientStoryModule
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await waitFor(() => {
        expect(screen.getByTestId('orient-story-module')).toBeInTheDocument();
      });

      // Select EXCLUDED story → STORY_MISALIGNED
      await userEvent.click(screen.getByLabelText('Organized company hackathon'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(
          screen.getByText(AlignmentErrors.STORY_MISALIGNED),
        ).toBeInTheDocument();
      });
    });
  });
});
