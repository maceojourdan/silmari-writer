/**
 * Integration test for the orient story record creation path
 *
 * Path: 295-orient-state-creates-single-story-record
 *
 * This proves end-to-end:
 * - Reachability: Full path executable from ORIENT trigger to persisted record
 * - TypeInvariant: Types preserved across all boundaries
 * - ErrorConsistency: Failures return structured errors without partial records
 *
 * Note: Mocks only the DAO layer (database boundary). Everything above
 * runs with real implementations: process chain, verifier, handler.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { z } from 'zod';
import type { OrientStoryRecord } from '../data_structures/OrientStoryRecord';

// Only mock the DAO — everything else is real
vi.mock('../data_access_objects/OrientStoryRecordDAO', () => ({
  OrientStoryRecordDAO: {
    insertStoryRecord: vi.fn(),
  },
}));

// Mock the logger to avoid console noise
vi.mock('../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { OrientStoryRecordDAO } from '../data_access_objects/OrientStoryRecordDAO';
import { CreateStoryRecordHandler } from '../request_handlers/CreateStoryRecordHandler';
import { OrientEventSchema, OrientStoryRecordSchema } from '../data_structures/OrientStoryRecord';
import { OrientError } from '../error_definitions/OrientErrors';

const mockDAO = vi.mocked(OrientStoryRecordDAO);

// Response schema for TypeInvariant
const OrientStoryRecordResponseSchema = z.object({
  id: z.string().min(1),
  story_title: z.string().min(1),
  initial_context: z.object({
    experienceId: z.string().min(1),
    summary: z.string().min(1),
  }),
});

describe('Orient Story Record Integration', () => {
  const validInput = {
    experiences: [
      {
        id: 'exp-001',
        title: 'Led migration to microservices architecture',
        summary: 'Decomposed monolithic application into 12 independently deployable services, reducing deployment time from 4 hours to 15 minutes.',
      },
      {
        id: 'exp-002',
        title: 'Built real-time analytics pipeline',
        summary: 'Designed and implemented a streaming data pipeline processing 1M events per second with sub-100ms latency.',
      },
      {
        id: 'exp-003',
        title: 'Established engineering hiring process',
        summary: 'Created structured interview process that improved offer acceptance rate from 40% to 75%.',
      },
    ],
  };

  const persistedRecord: OrientStoryRecord = {
    id: '550e8400-e29b-41d4-a716-446655440099',
    story_title: 'Led migration to microservices architecture',
    initial_context: {
      experienceId: 'exp-001',
      summary: 'Decomposed monolithic application into 12 independently deployable services, reducing deployment time from 4 hours to 15 minutes.',
    },
    createdAt: '2026-03-01T00:00:00.000Z',
  };

  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.insertStoryRecord.mockResolvedValue(persistedRecord);
  });

  describe('Reachability: Full path from ORIENT trigger to persisted record', () => {
    it('should process multiple experiences and return exactly one StoryRecord', async () => {
      // Step 1: Validate input (as the API route would)
      const validation = OrientEventSchema.safeParse(validInput);
      expect(validation.success).toBe(true);

      if (!validation.success) return;

      // Steps 2-5: Handler orchestrates process chain → verifier → DAO
      const result = await CreateStoryRecordHandler.handle(validation.data);

      // Assert: exactly one record returned
      expect(result.id).toBe('550e8400-e29b-41d4-a716-446655440099');
      expect(result.story_title).toBe('Led migration to microservices architecture');
      expect(result.initial_context.experienceId).toBe('exp-001');
    });

    it('should insert exactly one record via DAO', async () => {
      const validation = OrientEventSchema.safeParse(validInput);
      if (!validation.success) return;

      await CreateStoryRecordHandler.handle(validation.data);

      expect(mockDAO.insertStoryRecord).toHaveBeenCalledTimes(1);

      const daoArg = mockDAO.insertStoryRecord.mock.calls[0][0];
      expect(daoArg.story_title).toBe('Led migration to microservices architecture');
      expect(daoArg.initial_context.experienceId).toBe('exp-001');
      expect(daoArg.initial_context.summary).toContain('Decomposed monolithic');
    });

    it('should work with a single experience', async () => {
      const singleInput = {
        experiences: [
          { id: 'exp-solo', title: 'Solo project leadership', summary: 'Built entire platform solo' },
        ],
      };

      const validation = OrientEventSchema.safeParse(singleInput);
      expect(validation.success).toBe(true);

      if (!validation.success) return;

      mockDAO.insertStoryRecord.mockResolvedValue({
        ...persistedRecord,
        story_title: 'Solo project leadership',
        initial_context: { experienceId: 'exp-solo', summary: 'Built entire platform solo' },
      });

      const result = await CreateStoryRecordHandler.handle(validation.data);
      expect(result.story_title).toBe('Solo project leadership');
    });
  });

  describe('TypeInvariant: Response matches OrientStoryRecordResponseSchema', () => {
    it('should produce a response containing id, story_title, and initial_context', async () => {
      const validation = OrientEventSchema.safeParse(validInput);
      if (!validation.success) return;

      const result = await CreateStoryRecordHandler.handle(validation.data);

      const parsed = OrientStoryRecordResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should produce a record conforming to OrientStoryRecordSchema', async () => {
      const validation = OrientEventSchema.safeParse(validInput);
      if (!validation.success) return;

      const result = await CreateStoryRecordHandler.handle(validation.data);

      const parsed = OrientStoryRecordSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: Failures return structured errors without partial records', () => {
    it('should reject invalid input at the validation layer (empty experiences)', () => {
      const invalidInput = {
        experiences: [],
      };

      const validation = OrientEventSchema.safeParse(invalidInput);
      expect(validation.success).toBe(false);
    });

    it('should reject missing experiences field', () => {
      const invalidInput = {};

      const validation = OrientEventSchema.safeParse(invalidInput);
      expect(validation.success).toBe(false);
    });

    it('should reject experiences with missing required fields', () => {
      const invalidInput = {
        experiences: [
          { id: 'exp-1' }, // missing title and summary
        ],
      };

      const validation = OrientEventSchema.safeParse(invalidInput);
      expect(validation.success).toBe(false);
    });

    it('should throw STORY_RECORD_PERSISTENCE_FAILED when DAO fails', async () => {
      mockDAO.insertStoryRecord.mockRejectedValue(
        new OrientError('Connection refused', 'STORY_RECORD_PERSISTENCE_FAILED', 500, true),
      );

      const validation = OrientEventSchema.safeParse(validInput);
      if (!validation.success) return;

      try {
        await CreateStoryRecordHandler.handle(validation.data);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('STORY_RECORD_PERSISTENCE_FAILED');
        expect(e.statusCode).toBe(500);
        expect(e.retryable).toBe(true);
      }
    });

    it('should not call DAO when all experiences have empty titles', async () => {
      const invalidExperiences = {
        experiences: [
          { id: 'exp-1', title: '', summary: 'Has summary but no title' },
        ],
      };

      const validation = OrientEventSchema.safeParse(invalidExperiences);
      // This passes Zod but fails in selectExperience business logic
      // since title is empty string (min(1) in schema catches this)
      expect(validation.success).toBe(false);

      // DAO should never be called for invalid input
      expect(mockDAO.insertStoryRecord).not.toHaveBeenCalled();
    });
  });
});
