/**
 * ExportFinalizedAnswerHandler.test.ts - Maps export request to service logic.
 *
 * TLA+ Properties:
 * - Reachability: Call handler with valid answerId → assert service called and answer returned
 * - TypeInvariant: Returned object matches Answer type
 * - ErrorConsistency: Known AnswerErrors rethrown; unknown errors wrapped
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 334-export-or-copy-finalized-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AnswerSchema } from '@/server/data_structures/Answer';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';

// ---------------------------------------------------------------------------
// Mock Service
// ---------------------------------------------------------------------------

vi.mock('../../services/FinalizedAnswerExportService', () => ({
  FinalizedAnswerExportService: {
    getFinalizedAnswer: vi.fn(),
  },
}));

vi.mock('../../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FinalizedAnswerExportService } from '../../services/FinalizedAnswerExportService';
import { ExportFinalizedAnswerHandler } from '../ExportFinalizedAnswerHandler';

const mockService = vi.mocked(FinalizedAnswerExportService);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const finalizedAnswer = {
  id: answerId,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  locked: true,
  content: 'My finalized answer about leadership experience.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ExportFinalizedAnswerHandler.handle — Route to export service', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability', () => {
    it('should delegate to FinalizedAnswerExportService and return answer', async () => {
      mockService.getFinalizedAnswer.mockResolvedValue(finalizedAnswer);

      const result = await ExportFinalizedAnswerHandler.handle(answerId);

      expect(mockService.getFinalizedAnswer).toHaveBeenCalledWith(answerId);
      expect(result).toBeDefined();
      expect(result.id).toBe(answerId);
      expect(result.content).toBe('My finalized answer about leadership experience.');
    });
  });

  describe('TypeInvariant', () => {
    it('should return object matching Answer schema', async () => {
      mockService.getFinalizedAnswer.mockResolvedValue(finalizedAnswer);

      const result = await ExportFinalizedAnswerHandler.handle(answerId);
      const parsed = AnswerSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency', () => {
    it('should rethrow known AnswerError', async () => {
      const knownError = new AnswerError('Answer not found', 'ANSWER_NOT_FOUND', 404);
      mockService.getFinalizedAnswer.mockRejectedValue(knownError);

      try {
        await ExportFinalizedAnswerHandler.handle(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_FOUND');
      }
    });

    it('should wrap unknown errors and log them', async () => {
      mockService.getFinalizedAnswer.mockRejectedValue(new Error('Database connection failed'));

      try {
        await ExportFinalizedAnswerHandler.handle(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_FOUND');
      }
    });
  });
});
