/**
 * Tests for StorySelection - Step 2: Submit selected story confirmation
 *
 * Path: 313-confirm-aligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Select story → click confirm → confirmStory() called
 * - TypeInvariant: Payload matches ConfirmStoryRequestSchema
 * - ErrorConsistency:
 *   - No selection → confirm disabled + validation message
 *   - Mock 500 → UI shows submission failure message
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock fetch at network level
const mockFetch = vi.fn();

import { StorySelection } from '../StorySelection';
import { ConfirmStoryRequestSchema } from '@/server/data_structures/ConfirmStory';
import type { Story } from '@/server/data_structures/ConfirmStory';

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
  {
    id: 'story-003',
    title: 'Established engineering hiring process',
    summary: 'Created structured interview process across 3 departments.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
];

describe('StorySelection - Step 2: Submit selected story confirmation', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  describe('Reachability: Select story → confirm → API called', () => {
    it('should call confirmStory with { questionId, storyId } on confirm', async () => {
      const confirmedStory = {
        ...testStories[0],
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
        <StorySelection
          stories={testStories}
          questionId="q-001"
          onConfirmed={onConfirmed}
        />,
      );

      // Select the first story
      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));

      // Click confirm
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledWith('/api/story/confirm', expect.objectContaining({
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
        }));
      });

      // Verify the request body
      const call = mockFetch.mock.calls[0];
      const body = JSON.parse(call[1].body);
      expect(body).toEqual({ questionId: 'q-001', storyId: 'story-001' });
    });

    it('should call onConfirmed callback with confirmed story and excluded count', async () => {
      const confirmedStory = {
        ...testStories[0],
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
        <StorySelection
          stories={testStories}
          questionId="q-001"
          onConfirmed={onConfirmed}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(onConfirmed).toHaveBeenCalledWith(
          expect.objectContaining({ id: 'story-001', status: 'CONFIRMED' }),
          2,
        );
      });
    });
  });

  describe('TypeInvariant: Payload matches ConfirmStoryRequestSchema', () => {
    it('should produce a valid request payload', async () => {
      const payload = { questionId: 'q-001', storyId: 'story-001' };
      const parsed = ConfirmStoryRequestSchema.safeParse(payload);
      expect(parsed.success).toBe(true);
    });

    it('should reject payload with empty questionId', () => {
      const payload = { questionId: '', storyId: 'story-001' };
      const parsed = ConfirmStoryRequestSchema.safeParse(payload);
      expect(parsed.success).toBe(false);
    });

    it('should reject payload with empty storyId', () => {
      const payload = { questionId: 'q-001', storyId: '' };
      const parsed = ConfirmStoryRequestSchema.safeParse(payload);
      expect(parsed.success).toBe(false);
    });

    it('should reject payload missing storyId', () => {
      const payload = { questionId: 'q-001' };
      const parsed = ConfirmStoryRequestSchema.safeParse(payload);
      expect(parsed.success).toBe(false);
    });
  });

  describe('ErrorConsistency: Validation and server errors', () => {
    it('should disable confirm button when no story is selected', () => {
      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
        />,
      );

      const confirmBtn = screen.getByTestId('confirm-button');
      expect(confirmBtn).toBeDisabled();
    });

    it('should enable confirm button when a story is selected', async () => {
      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));

      const confirmBtn = screen.getByTestId('confirm-button');
      expect(confirmBtn).not.toBeDisabled();
    });

    it('should show submission failure message on 500 error', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({
          code: 'PERSISTENCE_FAILURE',
          message: 'Database write failed',
        }),
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByTestId('submission-error')).toBeInTheDocument();
        expect(screen.getByText(/Database write failed/i)).toBeInTheDocument();
      });
    });

    it('should show error on network failure', async () => {
      mockFetch.mockRejectedValueOnce(new TypeError('Failed to fetch'));

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByTestId('submission-error')).toBeInTheDocument();
      });
    });

    it('should re-enable confirm button after error', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({
          code: 'PERSISTENCE_FAILURE',
          message: 'Database write failed',
        }),
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      const confirmBtn = screen.getByTestId('confirm-button');
      await userEvent.click(confirmBtn);

      await waitFor(() => {
        expect(confirmBtn).not.toBeDisabled();
      });
    });
  });
});
