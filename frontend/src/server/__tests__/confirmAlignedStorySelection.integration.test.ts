/**
 * Integration test for the confirm-aligned-story-selection path
 *
 * Path: 313-confirm-aligned-story-selection
 *
 * This proves end-to-end:
 * - Reachability: Full path executable from load → confirm → persist → response
 * - TypeInvariant: Types preserved across all boundaries
 * - ErrorConsistency: Failures return structured errors without partial updates
 *
 * Note: Mocks only the DAO layer (database boundary). Everything above
 * runs with real implementations: service, verifier.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { z } from 'zod';

// Only mock the DAO — everything else is real
vi.mock('@/server/data_access_objects/ConfirmStoryDAO', () => ({
  ConfirmStoryDAO: {
    findQuestionById: vi.fn(),
    findJobRequirementsByQuestionId: vi.fn(),
    findStoriesByQuestionId: vi.fn(),
    findStoryById: vi.fn(),
    updateStatusesTransactional: vi.fn(),
  },
}));

import { ConfirmStoryDAO } from '@/server/data_access_objects/ConfirmStoryDAO';
import { ConfirmStoryService } from '@/server/services/ConfirmStoryService';
import { StoryAlignmentVerifier } from '@/server/verifiers/StoryAlignmentVerifier';
import {
  ConfirmStoryRequestSchema,
  ConfirmStoryResponseSchema,
  OrientStoryDataSchema,
  ValidationResultSchema,
} from '@/server/data_structures/ConfirmStory';
import { ConfirmStoryError } from '@/server/error_definitions/ConfirmStoryErrors';
import type { Question, Story, JobRequirement } from '@/server/data_structures/ConfirmStory';

const mockDAO = vi.mocked(ConfirmStoryDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const question: Question = {
  id: 'q-integration-001',
  text: 'Tell me about a time you led a cross-functional team to deliver a complex project under tight deadlines.',
  category: 'leadership',
};

const jobRequirements: JobRequirement[] = [
  {
    id: 'jr-int-001',
    description: 'Experience leading cross-functional teams of 5+ engineers',
    priority: 'REQUIRED',
  },
  {
    id: 'jr-int-002',
    description: 'Track record of delivering complex projects under tight deadlines',
    priority: 'REQUIRED',
  },
  {
    id: 'jr-int-003',
    description: 'Strong communication skills with stakeholders',
    priority: 'PREFERRED',
  },
];

const stories: Story[] = [
  {
    id: 'story-int-001',
    title: 'Led migration to microservices architecture',
    summary: 'Coordinated 4 teams across engineering, QA, and DevOps to decompose a monolithic application into 12 independently deployable services, reducing deployment time from 4 hours to 15 minutes.',
    status: 'AVAILABLE',
    questionId: 'q-integration-001',
  },
  {
    id: 'story-int-002',
    title: 'Built real-time analytics pipeline',
    summary: 'Designed and implemented a streaming data pipeline processing 1M events per second with sub-100ms latency, working across data engineering, platform, and product teams.',
    status: 'AVAILABLE',
    questionId: 'q-integration-001',
  },
  {
    id: 'story-int-003',
    title: 'Established engineering hiring process',
    summary: 'Created structured interview process that improved offer acceptance rate from 40% to 75%, coordinating with HR, engineering managers, and executive leadership.',
    status: 'AVAILABLE',
    questionId: 'q-integration-001',
  },
];

describe('Confirm Aligned Story Selection - Integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Setup DAO mocks with realistic data
    mockDAO.findQuestionById.mockResolvedValue(question);
    mockDAO.findJobRequirementsByQuestionId.mockResolvedValue(jobRequirements);
    mockDAO.findStoriesByQuestionId.mockResolvedValue(stories);
    mockDAO.findStoryById.mockImplementation(async (id: string) =>
      stories.find((s) => s.id === id) ?? null,
    );
    mockDAO.updateStatusesTransactional.mockImplementation(
      async (questionId: string, confirmedStoryId: string) => {
        const others = stories.filter((s) => s.id !== confirmedStoryId);
        return {
          confirmedStoryId,
          excludedCount: others.length,
        };
      },
    );
  });

  describe('Reachability: Full path from trigger to terminal condition', () => {
    it('should complete the full confirmation flow: load → validate → confirm → persist', async () => {
      // Step 1: Load context (simulating data loader)
      const orientData = {
        question,
        jobRequirements,
        stories,
      };

      // Validate loaded data
      const orientParsed = OrientStoryDataSchema.safeParse(orientData);
      expect(orientParsed.success).toBe(true);

      // Step 2: Validate request
      const confirmRequest = { questionId: 'q-integration-001', storyId: 'story-int-001' };
      const requestParsed = ConfirmStoryRequestSchema.safeParse(confirmRequest);
      expect(requestParsed.success).toBe(true);

      // Step 3: Validate alignment (verifier runs inside service)
      const validationResult = StoryAlignmentVerifier.validate(
        question,
        stories[0],
        jobRequirements,
        stories,
      );
      expect(validationResult.valid).toBe(true);

      // Step 4: Confirm via service (verifier + DAO orchestration)
      const result = await ConfirmStoryService.confirm(confirmRequest);

      // Assert: Exactly one story CONFIRMED
      expect(result.confirmedStoryId).toBe('story-int-001');
      expect(result.status).toBe('CONFIRMED');
      expect(result.story.id).toBe('story-int-001');
      expect(result.story.status).toBe('CONFIRMED');

      // Assert: Others excluded
      expect(result.excludedCount).toBe(2);

      // Assert: DAO was called correctly
      expect(mockDAO.updateStatusesTransactional).toHaveBeenCalledWith(
        'q-integration-001',
        'story-int-001',
      );
    });

    it('should work when confirming the second story instead', async () => {
      const result = await ConfirmStoryService.confirm({
        questionId: 'q-integration-001',
        storyId: 'story-int-002',
      });

      expect(result.confirmedStoryId).toBe('story-int-002');
      expect(result.status).toBe('CONFIRMED');
      expect(result.excludedCount).toBe(2);
    });

    it('should work when confirming the third story', async () => {
      const result = await ConfirmStoryService.confirm({
        questionId: 'q-integration-001',
        storyId: 'story-int-003',
      });

      expect(result.confirmedStoryId).toBe('story-int-003');
      expect(result.status).toBe('CONFIRMED');
      expect(result.excludedCount).toBe(2);
    });
  });

  describe('TypeInvariant: Types preserved across all boundaries', () => {
    it('should produce a response conforming to ConfirmStoryResponseSchema', async () => {
      const result = await ConfirmStoryService.confirm({
        questionId: 'q-integration-001',
        storyId: 'story-int-001',
      });

      const parsed = ConfirmStoryResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should produce valid ValidationResult from verifier', () => {
      const result = StoryAlignmentVerifier.validate(
        question,
        stories[0],
        jobRequirements,
        stories,
      );

      const parsed = ValidationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should produce valid OrientStoryData from context', () => {
      const data = { question, jobRequirements, stories };
      const parsed = OrientStoryDataSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: Structured errors without partial updates', () => {
    it('should reject confirmation of nonexistent story', async () => {
      mockDAO.findStoryById.mockResolvedValue(null);

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-integration-001',
          storyId: 'story-nonexistent',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('STORY_NOT_FOUND');
        expect(e.statusCode).toBe(404);
      }

      // DAO should NOT have been called for status update
      expect(mockDAO.updateStatusesTransactional).not.toHaveBeenCalled();
    });

    it('should reject confirmation of already confirmed story', async () => {
      const confirmedStory: Story = { ...stories[0], status: 'CONFIRMED' };
      mockDAO.findStoryById.mockResolvedValue(confirmedStory);
      mockDAO.findStoriesByQuestionId.mockResolvedValue([confirmedStory, ...stories.slice(1)]);

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-integration-001',
          storyId: 'story-int-001',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('STORY_ALREADY_CONFIRMED');
        expect(e.statusCode).toBe(409);
      }

      expect(mockDAO.updateStatusesTransactional).not.toHaveBeenCalled();
    });

    it('should reject confirmation when question not found', async () => {
      mockDAO.findQuestionById.mockResolvedValue(null);

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-nonexistent',
          storyId: 'story-int-001',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('DATA_NOT_FOUND');
        expect(e.statusCode).toBe(404);
      }

      expect(mockDAO.updateStatusesTransactional).not.toHaveBeenCalled();
    });

    it('should throw PERSISTENCE_FAILURE when DAO transaction fails', async () => {
      mockDAO.updateStatusesTransactional.mockRejectedValue(
        new Error('Connection refused'),
      );

      try {
        await ConfirmStoryService.confirm({
          questionId: 'q-integration-001',
          storyId: 'story-int-001',
        });
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e).toBeInstanceOf(ConfirmStoryError);
        expect(e.code).toBe('PERSISTENCE_FAILURE');
        expect(e.retryable).toBe(true);
      }
    });

    it('should reject invalid request schema at boundary', () => {
      const invalidRequest = { questionId: '', storyId: '' };
      const parsed = ConfirmStoryRequestSchema.safeParse(invalidRequest);
      expect(parsed.success).toBe(false);
    });
  });
});
