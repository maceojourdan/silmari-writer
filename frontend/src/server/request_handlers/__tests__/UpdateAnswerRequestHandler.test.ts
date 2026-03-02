/**
 * UpdateAnswerRequestHandler.test.ts - Path 337: Prevent Edit of Locked Answer
 *
 * TLA+ Properties:
 * - Reachability: Mock AnswerService.updateAnswer success → handler returns { id, content }
 * - TypeInvariant: Result matches UpdateAnswerResultSchema
 * - ErrorConsistency:
 *     - AnswerService throws AnswerError → rethrown as-is
 *     - AnswerService throws unknown Error → wrapped as SerializationError
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 337-prevent-edit-of-locked-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';
import { UpdateAnswerResultSchema } from '@/server/services/AnswerService';

// ---------------------------------------------------------------------------
// Mock Service
// ---------------------------------------------------------------------------

vi.mock('../../services/AnswerService', async () => {
  const { z } = await import('zod');
  return {
    AnswerService: {
      updateAnswer: vi.fn(),
    },
    UpdateAnswerResultSchema: z.object({
      id: z.string().uuid(),
      content: z.string(),
    }),
  };
});

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { AnswerService } from '../../services/AnswerService';
import { UpdateAnswerRequestHandler } from '../UpdateAnswerRequestHandler';

const mockService = vi.mocked(AnswerService);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const newContent = 'updated content';

const updateResult = {
  id: answerId,
  content: newContent,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('UpdateAnswerRequestHandler.handle — Path 337: Prevent Edit of Locked Answer', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call AnswerService.updateAnswer with id and content', async () => {
      mockService.updateAnswer.mockResolvedValue(updateResult);

      await UpdateAnswerRequestHandler.handle(answerId, newContent);

      expect(mockService.updateAnswer).toHaveBeenCalledWith(answerId, newContent);
    });

    it('should return the result from AnswerService', async () => {
      mockService.updateAnswer.mockResolvedValue(updateResult);

      const result = await UpdateAnswerRequestHandler.handle(answerId, newContent);

      expect(result).toEqual({
        id: answerId,
        content: newContent,
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching UpdateAnswerResultSchema', async () => {
      mockService.updateAnswer.mockResolvedValue(updateResult);

      const result = await UpdateAnswerRequestHandler.handle(answerId, newContent);
      const parsed = UpdateAnswerResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow known AnswerErrors without wrapping', async () => {
      const knownError = new AnswerError(
        'This answer has been finalized and cannot be modified.',
        'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
        403,
        false,
      );
      mockService.updateAnswer.mockRejectedValue(knownError);

      try {
        await UpdateAnswerRequestHandler.handle(answerId, newContent);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
        expect((e as AnswerError).statusCode).toBe(403);
      }
    });

    it('should wrap unknown errors as SerializationError', async () => {
      mockService.updateAnswer.mockRejectedValue(new TypeError('Cannot read properties'));

      try {
        await UpdateAnswerRequestHandler.handle(answerId, newContent);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('SERIALIZATION_ERROR');
        expect((e as AnswerError).statusCode).toBe(500);
      }
    });
  });
});
