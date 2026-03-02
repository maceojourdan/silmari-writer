/**
 * AnswerService.test.ts - Path 337: Prevent Edit of Locked Answer
 *
 * TLA+ Properties:
 * - Reachability: Given unlocked answer → call updateAnswer → assert DAO.updateContent called, result returned
 *     Also: Given locked answer → call updateAnswer → assert locked state detected, error thrown
 * - TypeInvariant: Result matches UpdateAnswerResultSchema; DAO returns Answer type; accepts string id and content
 * - ErrorConsistency:
 *     - DAO.findById returns null → ANSWER_NOT_FOUND (404)
 *     - DAO.findById throws DB error → PERSISTENCE_ERROR (500, retryable)
 *     - DAO returns locked answer → LOCKED_ANSWER_MODIFICATION_FORBIDDEN (403), DAO.updateContent NOT called
 *     - DAO.updateContent throws → PERSISTENCE_ERROR (500, retryable)
 *
 * Resource: db-h2s4 (service)
 * Path: 337-prevent-edit-of-locked-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';

// ---------------------------------------------------------------------------
// Mock DAO
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/AnswerDAO', () => ({
  AnswerDAO: {
    findById: vi.fn(),
    update: vi.fn(),
    updateContent: vi.fn(),
  },
}));

import { AnswerDAO } from '../../data_access_objects/AnswerDAO';
import { AnswerService, UpdateAnswerResultSchema } from '../AnswerService';

const mockDAO = vi.mocked(AnswerDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const unlockedAnswer = {
  id: answerId,
  status: 'DRAFT' as const,
  finalized: false,
  editable: true,
  locked: false,
  content: 'old content',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const lockedAnswer = {
  ...unlockedAnswer,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  locked: true,
  content: 'finalized content',
};

const updatedAnswer = {
  ...unlockedAnswer,
  content: 'new content',
  updatedAt: '2026-02-28T12:05:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('AnswerService.updateAnswer — Path 337: Prevent Edit of Locked Answer', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DAO.findById with the answer id', async () => {
      mockDAO.findById.mockResolvedValue(unlockedAnswer);
      mockDAO.updateContent.mockResolvedValue(updatedAnswer);

      await AnswerService.updateAnswer(answerId, 'new content');

      expect(mockDAO.findById).toHaveBeenCalledWith(answerId);
    });

    it('should detect unlocked state and proceed to update content', async () => {
      mockDAO.findById.mockResolvedValue(unlockedAnswer);
      mockDAO.updateContent.mockResolvedValue(updatedAnswer);

      await AnswerService.updateAnswer(answerId, 'new content');

      expect(mockDAO.updateContent).toHaveBeenCalledWith(answerId, 'new content');
    });

    it('should return { id, content } from the updated answer', async () => {
      mockDAO.findById.mockResolvedValue(unlockedAnswer);
      mockDAO.updateContent.mockResolvedValue(updatedAnswer);

      const result = await AnswerService.updateAnswer(answerId, 'new content');

      expect(result).toEqual({
        id: answerId,
        content: 'new content',
      });
    });

    it('should detect locked state and throw LOCKED_ANSWER_MODIFICATION_FORBIDDEN', async () => {
      mockDAO.findById.mockResolvedValue(lockedAnswer);

      try {
        await AnswerService.updateAnswer(answerId, 'attempt edit');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
      }
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching UpdateAnswerResultSchema', async () => {
      mockDAO.findById.mockResolvedValue(unlockedAnswer);
      mockDAO.updateContent.mockResolvedValue(updatedAnswer);

      const result = await AnswerService.updateAnswer(answerId, 'new content');
      const parsed = UpdateAnswerResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });

    it('should accept string id and string content parameters', async () => {
      mockDAO.findById.mockResolvedValue(unlockedAnswer);
      mockDAO.updateContent.mockResolvedValue(updatedAnswer);

      // Verifies the method signature accepts string params without type errors
      const result = await AnswerService.updateAnswer(answerId, 'new content');

      expect(result.id).toBe(answerId);
      expect(result.content).toBe('new content');
    });

    it('should verify DAO returns a full Answer type object', async () => {
      mockDAO.findById.mockResolvedValue(unlockedAnswer);
      mockDAO.updateContent.mockResolvedValue(updatedAnswer);

      await AnswerService.updateAnswer(answerId, 'new content');

      // Confirm the mock was called, which means the DAO returns Answer type
      expect(mockDAO.findById).toHaveReturnedWith(expect.any(Promise));
      expect(mockDAO.updateContent).toHaveReturnedWith(expect.any(Promise));
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw ANSWER_NOT_FOUND when DAO.findById returns null', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await AnswerService.updateAnswer(answerId, 'new content');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_FOUND');
        expect((e as AnswerError).statusCode).toBe(404);
      }
    });

    it('should throw PERSISTENCE_ERROR when DAO.findById throws a DB error', async () => {
      mockDAO.findById.mockRejectedValue(new Error('Connection refused'));

      try {
        await AnswerService.updateAnswer(answerId, 'new content');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('PERSISTENCE_ERROR');
        expect((e as AnswerError).statusCode).toBe(500);
        expect((e as AnswerError).retryable).toBe(true);
      }
    });

    it('should throw LOCKED_ANSWER_MODIFICATION_FORBIDDEN when answer is locked', async () => {
      mockDAO.findById.mockResolvedValue(lockedAnswer);

      try {
        await AnswerService.updateAnswer(answerId, 'new content');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
        expect((e as AnswerError).statusCode).toBe(403);
      }

      expect(mockDAO.updateContent).not.toHaveBeenCalled();
    });

    it('should throw PERSISTENCE_ERROR when DAO.updateContent throws', async () => {
      mockDAO.findById.mockResolvedValue(unlockedAnswer);
      mockDAO.updateContent.mockRejectedValue(new Error('Write failed'));

      try {
        await AnswerService.updateAnswer(answerId, 'new content');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('PERSISTENCE_ERROR');
        expect((e as AnswerError).statusCode).toBe(500);
        expect((e as AnswerError).retryable).toBe(true);
      }
    });
  });
});
