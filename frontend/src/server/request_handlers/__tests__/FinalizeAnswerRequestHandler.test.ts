/**
 * FinalizeAnswerRequestHandler.test.ts - Step 4: Return Finalized State to Frontend
 *
 * TLA+ Properties:
 * - Reachability: Mock service success → expect JSON { id, finalized: true, editable: false }
 * - TypeInvariant: Response matches FinalizeAnswerResult schema
 * - ErrorConsistency: Simulate serialization throw → expect 500 with FinalizeAnswerErrors.SERIALIZATION_ERROR
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 333-finalize-answer-locks-editing
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeAnswerResultSchema } from '@/server/data_structures/Answer';
import { FinalizeAnswerError } from '@/server/error_definitions/FinalizeAnswerErrors';

// ---------------------------------------------------------------------------
// Mock Service
// ---------------------------------------------------------------------------

vi.mock('../../services/AnswerFinalizeService', () => ({
  AnswerFinalizeService: {
    finalize: vi.fn(),
  },
}));

import { AnswerFinalizeService } from '../../services/AnswerFinalizeService';
import { FinalizeAnswerRequestHandler } from '../FinalizeAnswerRequestHandler';

const mockService = vi.mocked(AnswerFinalizeService);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const finalizeResult = {
  id: answerId,
  finalized: true as const,
  editable: false as const,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeAnswerRequestHandler.handle — Step 4: Return Finalized State', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return JSON { id, finalized: true, editable: false } on service success', async () => {
      mockService.finalize.mockResolvedValue(finalizeResult);

      const result = await FinalizeAnswerRequestHandler.handle(answerId);

      expect(mockService.finalize).toHaveBeenCalledWith(answerId);
      expect(result).toEqual({
        id: answerId,
        finalized: true,
        editable: false,
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching FinalizeAnswerResult schema', async () => {
      mockService.finalize.mockResolvedValue(finalizeResult);

      const result = await FinalizeAnswerRequestHandler.handle(answerId);
      const parsed = FinalizeAnswerResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SERIALIZATION_ERROR when serialization fails', async () => {
      // Simulate a service that returns a value that causes serialization to fail
      mockService.finalize.mockRejectedValue(new TypeError('Cannot serialize'));

      try {
        await FinalizeAnswerRequestHandler.handle(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeAnswerError);
        expect((e as FinalizeAnswerError).code).toBe('SERIALIZATION_ERROR');
        expect((e as FinalizeAnswerError).statusCode).toBe(500);
      }
    });

    it('should rethrow known FinalizeAnswerErrors without wrapping', async () => {
      const knownError = new FinalizeAnswerError('Answer not found', 'ANSWER_NOT_FOUND', 404, false);
      mockService.finalize.mockRejectedValue(knownError);

      try {
        await FinalizeAnswerRequestHandler.handle(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeAnswerError);
        expect((e as FinalizeAnswerError).code).toBe('ANSWER_NOT_FOUND');
        expect((e as FinalizeAnswerError).statusCode).toBe(404);
      }
    });
  });
});
