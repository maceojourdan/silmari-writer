/**
 * Tests for ConfirmStoryService - Step 4: Mark story as confirmed and restrict scope
 *
 * Path: 313-confirm-aligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Seed 3 stories → confirm 1 → one CONFIRMED, others EXCLUDED
 * - TypeInvariant: Service returns ConfirmStoryResponse schema
 * - ErrorConsistency: DAO failure mid-transaction → no status changed (rollback)
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { z } from 'zod';

// Mock DAO
vi.mock('@/server/data_access_objects/ConfirmStoryDAO', () => ({
  ConfirmStoryDAO: {
    findQuestionById: vi.fn(),
    findJobRequirementsByQuestionId: vi.fn(),
    findStoriesByQuestionId: vi.fn(),
    findStoryById: vi.fn(),
    updateStatusesTransactional: vi.fn(),
  },
}));

import { ConfirmStoryService } from '../ConfirmStoryService';
import { ConfirmStoryDAO } from '@/server/data_access_objects/ConfirmStoryDAO';
import { ConfirmStoryResponseSchema } from '@/server/data_structures/ConfirmStory';
import { ConfirmStoryError } from '@/server/error_definitions/ConfirmStoryErrors';
import type { Question, Story, JobRequirement } from '@/server/data_structures/ConfirmStory';

const mockDAO = vi.mocked(ConfirmStoryDAO);

const question: Question = {
  id: 'q-001',
  text: 'Tell me about a time you led a cross-functional team.',
  category: 'leadership',
};

const requirements: JobRequirement[] = [
  { id: 'jr-001', description: 'Experience leading cross-functional teams', priority: 'REQUIRED' },
];

const stories: Story[] = [
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
  {
    id: 'story-003',
    title: 'Established engineering hiring process',
    summary: 'Created interview process.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
];

describe('ConfirmStoryService - Step 4: Mark story as confirmed', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default mock setup
    mockDAO.findQuestionById.mockResolvedValue(question);
    mockDAO.findJobRequirementsByQuestionId.mockResolvedValue(requirements);
    mockDAO.findStoriesByQuestionId.mockResolvedValue(stories);
    mockDAO.findStoryById.mockResolvedValue(stories[0]);
    mockDAO.updateStatusesTransactional.mockResolvedValue({
      confirmedStoryId: 'story-001',
      excludedCount: 2,
    });
  });

  describe('Reachability: Confirm 1 of 3 stories', () => {
    it('should confirm the selected story and exclude others', async () => {
      const result = await ConfirmStoryService.confirm({
        questionId: 'q-001',
        storyId: 'story-001',
      });

      expect(result.confirmedStoryId).toBe('story-001');
      expect(result.status).toBe('CONFIRMED');
      expect(result.excludedCount).toBe(2);
    });

    it('should call DAO.updateStatusesTransactional with correct args', async () => {
      await ConfirmStoryService.confirm({
        questionId: 'q-001',
        storyId: 'story-001',
      });

      expect(mockDAO.updateStatusesTransactional).toHaveBeenCalledWith(
        'q-001',
        'story-001',
      );
    });

    it('should validate the story exists and is aligned before confirming', async () => {
      await ConfirmStoryService.confirm({
        questionId: 'q-001',
        storyId: 'story-001',
      });

      // Verifier should have been called (implicitly via findStoryById + findStoriesByQuestionId)
      expect(mockDAO.findStoryById).toHaveBeenCalledWith('story-001');
      expect(mockDAO.findStoriesByQuestionId).toHaveBeenCalledWith('q-001');
    });
  });

  describe('TypeInvariant: Response matches ConfirmStoryResponseSchema', () => {
    it('should return a value conforming to ConfirmStoryResponseSchema', async () => {
      const result = await ConfirmStoryService.confirm({
        questionId: 'q-001',
        storyId: 'story-001',
      });

      const parsed = ConfirmStoryResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: Failure scenarios', () => {
    it('should throw STORY_NOT_FOUND when story does not exist', async () => {
      mockDAO.findStoryById.mockResolvedValue(null);

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-001',
          storyId: 'story-999',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('STORY_NOT_FOUND');
      }
    });

    it('should throw STORY_ALREADY_CONFIRMED when story is already confirmed', async () => {
      const confirmedStory: Story = { ...stories[0], status: 'CONFIRMED' };
      mockDAO.findStoryById.mockResolvedValue(confirmedStory);
      mockDAO.findStoriesByQuestionId.mockResolvedValue([confirmedStory, ...stories.slice(1)]);

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-001',
          storyId: 'story-001',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('STORY_ALREADY_CONFIRMED');
      }
    });

    it('should throw PERSISTENCE_FAILURE when DAO transaction fails', async () => {
      mockDAO.updateStatusesTransactional.mockRejectedValue(
        new Error('Connection refused'),
      );

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-001',
          storyId: 'story-001',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('PERSISTENCE_FAILURE');
      }
    });

    it('should throw DATA_NOT_FOUND when question does not exist', async () => {
      mockDAO.findQuestionById.mockResolvedValue(null);

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-999',
          storyId: 'story-001',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('DATA_NOT_FOUND');
      }
    });

    it('should not call updateStatusesTransactional when validation fails', async () => {
      mockDAO.findStoryById.mockResolvedValue(null);

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-001',
          storyId: 'story-999',
        });
      } catch {
        // Expected
      }

      expect(mockDAO.updateStatusesTransactional).not.toHaveBeenCalled();
    });
  });
});
