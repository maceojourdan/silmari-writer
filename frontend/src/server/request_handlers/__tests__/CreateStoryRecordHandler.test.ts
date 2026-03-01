/**
 * Tests for CreateStoryRecordHandler
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 295-orient-state-creates-single-story-record
 *
 * TLA+ properties tested:
 * - Reachability: Mock process chain → validator → DAO, call handler with ORIENT event → 200 with StoryRecord JSON
 * - TypeInvariant: Response body includes id, story_title, initial_context
 * - ErrorConsistency: Simulate error → structured OrientError or GenericError payload
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { z } from 'zod';
import { OrientError } from '../../error_definitions/OrientErrors';
import { GenericError } from '../../error_definitions/GenericErrors';
import type { OrientStoryRecord } from '../../data_structures/OrientStoryRecord';

// Mock the process chain
vi.mock('../../process_chains/OrientProcessChain', () => ({
  OrientProcessChain: {
    startOrientProcess: vi.fn(),
    selectExperience: vi.fn(),
  },
}));

// Mock the verifier
vi.mock('../../verifiers/StoryRecordVerifier', () => ({
  StoryRecordVerifier: {
    validateStoryRecord: vi.fn(),
  },
}));

// Mock the DAO
vi.mock('../../data_access_objects/OrientStoryRecordDAO', () => ({
  OrientStoryRecordDAO: {
    insertStoryRecord: vi.fn(),
  },
}));

// Mock the logger
vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { OrientProcessChain } from '../../process_chains/OrientProcessChain';
import { StoryRecordVerifier } from '../../verifiers/StoryRecordVerifier';
import { OrientStoryRecordDAO } from '../../data_access_objects/OrientStoryRecordDAO';
import { logger } from '../../logging/logger';
import { CreateStoryRecordHandler } from '../CreateStoryRecordHandler';

const mockProcessChain = vi.mocked(OrientProcessChain);
const mockVerifier = vi.mocked(StoryRecordVerifier);
const mockDAO = vi.mocked(OrientStoryRecordDAO);
const mockLogger = vi.mocked(logger);

// Response schema for TypeInvariant
const StoryRecordResponseSchema = z.object({
  id: z.string().min(1),
  story_title: z.string().min(1),
  initial_context: z.object({
    experienceId: z.string().min(1),
    summary: z.string().min(1),
  }),
});

describe('CreateStoryRecordHandler', () => {
  const orientEvent = {
    experiences: [
      { id: 'exp-1', title: 'Led migration to microservices', summary: 'Broke monolith into 12 services' },
      { id: 'exp-2', title: 'Built real-time analytics', summary: 'Streaming pipeline' },
    ],
  };

  const executionContext = {
    experiences: orientEvent.experiences,
  };

  const creationPayload = {
    story_title: 'Led migration to microservices',
    initial_context: {
      experienceId: 'exp-1',
      summary: 'Broke monolith into 12 services',
    },
  };

  const validatedRecord: OrientStoryRecord = {
    story_title: 'Led migration to microservices',
    initial_context: {
      experienceId: 'exp-1',
      summary: 'Broke monolith into 12 services',
    },
  };

  const persistedRecord: OrientStoryRecord = {
    ...validatedRecord,
    id: '550e8400-e29b-41d4-a716-446655440099',
    createdAt: '2026-03-01T00:00:00.000Z',
  };

  function setupSuccessfulMocks() {
    mockProcessChain.startOrientProcess.mockReturnValue(executionContext);
    mockProcessChain.selectExperience.mockReturnValue(creationPayload);
    mockVerifier.validateStoryRecord.mockReturnValue(validatedRecord);
    mockDAO.insertStoryRecord.mockResolvedValue(persistedRecord);
  }

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: ORIENT event → handler orchestrates full chain → returns StoryRecord', () => {
    it('should orchestrate process chain → verifier → DAO and return persisted record', async () => {
      setupSuccessfulMocks();

      const result = await CreateStoryRecordHandler.handle(orientEvent);

      expect(mockProcessChain.startOrientProcess).toHaveBeenCalledWith(orientEvent);
      expect(mockProcessChain.selectExperience).toHaveBeenCalledWith(executionContext);
      expect(mockVerifier.validateStoryRecord).toHaveBeenCalledWith(creationPayload);
      expect(mockDAO.insertStoryRecord).toHaveBeenCalledWith(validatedRecord);
      expect(result).toEqual(persistedRecord);
    });

    it('should return record with id and story_title', async () => {
      setupSuccessfulMocks();

      const result = await CreateStoryRecordHandler.handle(orientEvent);

      expect(result.id).toBe('550e8400-e29b-41d4-a716-446655440099');
      expect(result.story_title).toBe('Led migration to microservices');
    });
  });

  describe('TypeInvariant: response body includes id, story_title, initial_context', () => {
    it('should return response matching StoryRecordResponseSchema', async () => {
      setupSuccessfulMocks();

      const result = await CreateStoryRecordHandler.handle(orientEvent);

      const parsed = StoryRecordResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: errors → structured error responses', () => {
    it('should rethrow OrientError as-is', async () => {
      const { OrientErrors } = await import('../../error_definitions/OrientErrors');
      mockProcessChain.startOrientProcess.mockImplementation(() => {
        throw OrientErrors.SystemProcessChainNotFound();
      });

      await expect(CreateStoryRecordHandler.handle(orientEvent)).rejects.toThrow(
        OrientError,
      );
    });

    it('should preserve OrientError code when rethrowing', async () => {
      const { OrientErrors } = await import('../../error_definitions/OrientErrors');
      mockProcessChain.selectExperience.mockImplementation(() => {
        throw OrientErrors.NoValidExperienceSelected();
      });
      mockProcessChain.startOrientProcess.mockReturnValue(executionContext);

      try {
        await CreateStoryRecordHandler.handle(orientEvent);
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(OrientError);
        expect((e as OrientError).code).toBe('NO_VALID_EXPERIENCE_SELECTED');
      }
    });

    it('should wrap unexpected errors in GenericError and log', async () => {
      mockProcessChain.startOrientProcess.mockImplementation(() => {
        throw new TypeError('undefined is not a function');
      });

      await expect(CreateStoryRecordHandler.handle(orientEvent)).rejects.toThrow(
        GenericError,
      );

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should set GenericError code to INTERNAL_ERROR for unexpected errors', async () => {
      mockProcessChain.startOrientProcess.mockImplementation(() => {
        throw new Error('Unexpected');
      });

      try {
        await CreateStoryRecordHandler.handle(orientEvent);
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }
    });
  });
});
