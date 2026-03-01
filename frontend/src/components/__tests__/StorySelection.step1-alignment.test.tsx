/**
 * Tests for StorySelection - Step 1: Capture confirm action
 *
 * Path: 314-prevent-confirmation-of-misaligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Select story → click confirm → AlignmentVerifier.validate() called with payload
 * - TypeInvariant: Payload shape matches ConfirmationPayload
 * - ErrorConsistency: No selection → AlignmentVerifier NOT called, generic validation message shown
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock AlignmentVerifier
vi.mock('@/verifiers/AlignmentVerifier', () => ({
  AlignmentVerifier: {
    validate: vi.fn().mockReturnValue({ status: 'aligned' }),
  },
}));

// Mock fetch at network level (for the confirmStory API call after alignment passes)
const mockFetch = vi.fn();

import { StorySelection } from '../StorySelection';
import { AlignmentVerifier } from '@/verifiers/AlignmentVerifier';
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

describe('StorySelection - Step 1: Capture confirm action', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    mockValidate.mockReset();
    mockValidate.mockReturnValue({ status: 'aligned' });

    // Mock successful API response for when alignment passes
    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        confirmedStoryId: 'story-001',
        status: 'CONFIRMED',
        story: { ...testStories[0], status: 'CONFIRMED' },
        excludedCount: 1,
      }),
    });
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call AlignmentVerifier.validate() with correct payload when confirm is clicked', async () => {
      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      // Select the first story
      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      // Click confirm
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(mockValidate).toHaveBeenCalledTimes(1);
      });

      const [payload, rules] = mockValidate.mock.calls[0];
      expect(payload).toEqual({
        storyId: 'story-001',
        questionId: 'q-001',
        jobId: 'job-001',
      });
      // Rules should be provided (not null)
      expect(rules).not.toBeNull();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should construct payload with storyId, questionId, and jobId', async () => {
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
        expect(mockValidate).toHaveBeenCalledTimes(1);
      });

      const [payload] = mockValidate.mock.calls[0];
      expect(payload).toHaveProperty('storyId');
      expect(payload).toHaveProperty('questionId');
      expect(payload).toHaveProperty('jobId');
      expect(typeof payload.storyId).toBe('string');
      expect(typeof payload.questionId).toBe('string');
      expect(typeof payload.jobId).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should NOT call AlignmentVerifier.validate when no story is selected', async () => {
      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      // Confirm button is disabled when no story is selected, so we can't click it normally.
      // But the plan says: "Render without selectedStory → Click Confirm → validate NOT called"
      // The button is disabled, so the handler shouldn't fire
      const confirmBtn = screen.getByTestId('confirm-button');
      expect(confirmBtn).toBeDisabled();
      expect(mockValidate).not.toHaveBeenCalled();
    });
  });
});
