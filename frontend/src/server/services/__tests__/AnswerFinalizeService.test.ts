/**
 * AnswerFinalizeService.test.ts - Step 3: Validate and Lock Answer
 *
 * TLA+ Properties:
 * - Reachability: Given completed, editable answer → call finalize → assert DAO.update called with { finalized: true, editable: false }
 * - TypeInvariant: Returned entity matches Answer type (id, finalized:boolean, editable:boolean)
 * - ErrorConsistency:
 *     - Not found → FinalizeAnswerErrors.ANSWER_NOT_FOUND
 *     - Not completed → FinalizeAnswerErrors.ANSWER_NOT_COMPLETED
 *     - Already finalized → FinalizeAnswerErrors.ANSWER_ALREADY_FINALIZED
 *     - Assert DAO.update NOT called in error cases
 *
 * Resource: db-h2s4 (service)
 * Path: 333-finalize-answer-locks-editing
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeAnswerResultSchema } from '@/server/data_structures/Answer';
import { FinalizeAnswerError } from '@/server/error_definitions/FinalizeAnswerErrors';

// ---------------------------------------------------------------------------
// Mock DAO
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/AnswerDAO', () => ({
  AnswerDAO: {
    findById: vi.fn(),
    update: vi.fn(),
  },
}));

import { AnswerDAO } from '../../data_access_objects/AnswerDAO';
import { AnswerFinalizeService } from '../AnswerFinalizeService';

const mockDAO = vi.mocked(AnswerDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const completedEditableAnswer = {
  id: answerId,
  status: 'COMPLETED' as const,
  finalized: false,
  editable: true,
  content: 'My completed answer content',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const finalizedAnswer = {
  ...completedEditableAnswer,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  updatedAt: '2026-02-28T12:01:00.000Z',
};

const draftAnswer = {
  ...completedEditableAnswer,
  status: 'DRAFT' as const,
};

const alreadyFinalizedAnswer = {
  ...completedEditableAnswer,
  status: 'COMPLETED' as const,
  finalized: true,
  editable: false,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('AnswerFinalizeService.finalize — Step 3: Validate and Lock Answer', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DAO.update with { finalized: true, editable: false } for completed editable answer', async () => {
      mockDAO.findById.mockResolvedValue(completedEditableAnswer);
      mockDAO.update.mockResolvedValue(finalizedAnswer);

      const result = await AnswerFinalizeService.finalize(answerId);

      expect(mockDAO.findById).toHaveBeenCalledWith(answerId);
      expect(mockDAO.update).toHaveBeenCalledWith(answerId, {
        finalized: true,
        editable: false,
        status: 'FINALIZED',
      });
      expect(result).toBeDefined();
      expect(result.finalized).toBe(true);
      expect(result.editable).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching FinalizeAnswerResult schema', async () => {
      mockDAO.findById.mockResolvedValue(completedEditableAnswer);
      mockDAO.update.mockResolvedValue(finalizedAnswer);

      const result = await AnswerFinalizeService.finalize(answerId);
      const parsed = FinalizeAnswerResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw ANSWER_NOT_FOUND when DAO returns null', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await AnswerFinalizeService.finalize(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeAnswerError);
        expect((e as FinalizeAnswerError).code).toBe('ANSWER_NOT_FOUND');
        expect((e as FinalizeAnswerError).statusCode).toBe(404);
      }

      expect(mockDAO.update).not.toHaveBeenCalled();
    });

    it('should throw ANSWER_NOT_COMPLETED when answer is in DRAFT status', async () => {
      mockDAO.findById.mockResolvedValue(draftAnswer);

      try {
        await AnswerFinalizeService.finalize(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeAnswerError);
        expect((e as FinalizeAnswerError).code).toBe('ANSWER_NOT_COMPLETED');
        expect((e as FinalizeAnswerError).statusCode).toBe(422);
      }

      expect(mockDAO.update).not.toHaveBeenCalled();
    });

    it('should throw ANSWER_ALREADY_FINALIZED when answer is already finalized', async () => {
      mockDAO.findById.mockResolvedValue(alreadyFinalizedAnswer);

      try {
        await AnswerFinalizeService.finalize(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeAnswerError);
        expect((e as FinalizeAnswerError).code).toBe('ANSWER_ALREADY_FINALIZED');
        expect((e as FinalizeAnswerError).statusCode).toBe(409);
      }

      expect(mockDAO.update).not.toHaveBeenCalled();
    });
  });
});
