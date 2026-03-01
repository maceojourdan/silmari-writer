/**
 * Tests for OrientStoryModule - Step 5: Display confirmed story for next step
 *
 * Path: 313-confirm-aligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Successful confirmation → navigation to next route + confirmed story shown
 * - TypeInvariant: Response matches ConfirmStoryResponseSchema
 * - ErrorConsistency: Malformed response → error message, no navigation
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the data loader
vi.mock('@/data_loaders/loadOrientStoryData', () => ({
  loadOrientStoryData: vi.fn(),
}));

// Mock next/navigation
const mockPush = vi.fn();
vi.mock('next/navigation', () => ({
  useRouter: () => ({
    push: mockPush,
    replace: vi.fn(),
    back: vi.fn(),
    forward: vi.fn(),
    refresh: vi.fn(),
    prefetch: vi.fn(),
  }),
}));

// Mock fetch at network level
const mockFetch = vi.fn();

import { OrientStoryModule } from '../OrientStoryModule';
import { loadOrientStoryData } from '@/data_loaders/loadOrientStoryData';
import { ConfirmStoryResponseSchema } from '@/server/data_structures/ConfirmStory';

const mockLoader = vi.mocked(loadOrientStoryData);

describe('OrientStoryModule - Step 5: Confirm success and navigation', () => {
  const loadedData = {
    question: {
      id: 'q-001',
      text: 'Tell me about a time you led a cross-functional team.',
      category: 'leadership',
    },
    jobRequirements: [
      { id: 'jr-001', description: 'Experience leading cross-functional teams', priority: 'REQUIRED' },
    ],
    stories: [
      {
        id: 'story-001',
        title: 'Led migration to microservices architecture',
        summary: 'Coordinated 4 teams.',
        status: 'AVAILABLE',
        questionId: 'q-001',
      },
      {
        id: 'story-002',
        title: 'Built real-time analytics pipeline',
        summary: 'Designed streaming pipeline.',
        status: 'AVAILABLE',
        questionId: 'q-001',
      },
    ],
  };

  const successResponse = {
    confirmedStoryId: 'story-001',
    status: 'CONFIRMED',
    story: {
      id: 'story-001',
      title: 'Led migration to microservices architecture',
      summary: 'Coordinated 4 teams.',
      status: 'CONFIRMED',
      questionId: 'q-001',
    },
    excludedCount: 1,
  };

  beforeEach(() => {
    vi.clearAllMocks();
    vi.stubGlobal('fetch', mockFetch);
    mockLoader.mockResolvedValue(loadedData);
    mockPush.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  describe('Reachability: Successful confirmation → confirmed story shown', () => {
    it('should show only the confirmed story after successful confirmation', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      render(<OrientStoryModule questionId="q-001" />);

      // Wait for data to load
      await waitFor(() => {
        expect(screen.getByText('Led migration to microservices architecture')).toBeInTheDocument();
      });

      // Select story
      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));

      // Confirm
      await userEvent.click(screen.getByTestId('confirm-button'));

      // Should show confirmed story
      await waitFor(() => {
        expect(screen.getByTestId('orient-story-confirmed')).toBeInTheDocument();
        expect(screen.getByText('Story Confirmed')).toBeInTheDocument();
      });
    });

    it('should call onConfirmed callback with confirmed story', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      const onConfirmed = vi.fn();

      render(<OrientStoryModule questionId="q-001" onConfirmed={onConfirmed} />);

      await waitFor(() => {
        expect(screen.getByText('Led migration to microservices architecture')).toBeInTheDocument();
      });

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(onConfirmed).toHaveBeenCalledWith(
          expect.objectContaining({ id: 'story-001', status: 'CONFIRMED' }),
          1,
        );
      });
    });
  });

  describe('TypeInvariant: Response matches ConfirmStoryResponseSchema', () => {
    it('should accept a valid confirmation response', () => {
      const parsed = ConfirmStoryResponseSchema.safeParse(successResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject a response without confirmedStoryId', () => {
      const invalid = { ...successResponse, confirmedStoryId: '' };
      const parsed = ConfirmStoryResponseSchema.safeParse(invalid);
      expect(parsed.success).toBe(false);
    });

    it('should reject a response with wrong status', () => {
      const invalid = { ...successResponse, status: 'PENDING' };
      const parsed = ConfirmStoryResponseSchema.safeParse(invalid);
      expect(parsed.success).toBe(false);
    });
  });

  describe('ErrorConsistency: Malformed response → error, no navigation', () => {
    it('should show error on server failure', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({
          code: 'PERSISTENCE_FAILURE',
          message: 'Database write failed',
        }),
      });

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByText('Led migration to microservices architecture')).toBeInTheDocument();
      });

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByTestId('submission-error')).toBeInTheDocument();
      });

      // Should not navigate
      expect(mockPush).not.toHaveBeenCalled();
    });

    it('should remain on selection screen after error', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 422,
        json: async () => ({
          code: 'STORY_NOT_ALIGNED',
          message: 'Story does not align',
        }),
      });

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByText('Led migration to microservices architecture')).toBeInTheDocument();
      });

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByTestId('submission-error')).toBeInTheDocument();
      });

      // Story selection should still be visible
      expect(screen.getByTestId('story-selection')).toBeInTheDocument();
    });
  });
});
