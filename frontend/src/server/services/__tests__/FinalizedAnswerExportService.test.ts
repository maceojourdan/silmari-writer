/**
 * FinalizedAnswerExportService.test.ts - Step 2: Load finalized answer content
 *
 * TLA+ Properties:
 * Test 2A (happy path):
 * - Reachability: Call service with valid answerId; mock DAO to return Answer{ status: FINALIZED, locked: true }
 * - TypeInvariant: Assert returned object matches Answer type from db-f8n5
 * - ErrorConsistency: N/A (happy path)
 *
 * Test 2B (error cases):
 * - DAO returns null → expect AnswerErrors.ANSWER_NOT_FOUND
 * - DAO returns status != FINALIZED or locked=false → expect AnswerErrors.ANSWER_NOT_LOCKED
 *
 * Resource: db-h2s4 (service)
 * Path: 334-export-or-copy-finalized-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AnswerSchema } from '@/server/data_structures/Answer';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';

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
import { FinalizedAnswerExportService } from '../FinalizedAnswerExportService';

const mockDAO = vi.mocked(AnswerDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const finalizedLockedAnswer = {
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

const completedUnlockedAnswer = {
  id: answerId,
  status: 'COMPLETED' as const,
  finalized: false,
  editable: true,
  locked: false,
  content: 'My completed answer content.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const finalizedNotLockedAnswer = {
  id: answerId,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  locked: false,
  content: 'My finalized but not locked answer.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizedAnswerExportService.getFinalizedAnswer — Step 2: Load finalized answer content', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Test 2A: Happy path
  // -------------------------------------------------------------------------

  describe('Test 2A: Happy path', () => {
    // Reachability
    it('should call DAO.findById and return full answer when finalized and locked', async () => {
      mockDAO.findById.mockResolvedValue(finalizedLockedAnswer);

      const result = await FinalizedAnswerExportService.getFinalizedAnswer(answerId);

      expect(mockDAO.findById).toHaveBeenCalledWith(answerId);
      expect(result).toBeDefined();
      expect(result.id).toBe(answerId);
      expect(result.content).toBe('My finalized answer about leadership experience.');
      expect(result.finalized).toBe(true);
      expect(result.locked).toBe(true);
    });

    // TypeInvariant
    it('should return object matching Answer schema from db-f8n5', async () => {
      mockDAO.findById.mockResolvedValue(finalizedLockedAnswer);

      const result = await FinalizedAnswerExportService.getFinalizedAnswer(answerId);
      const parsed = AnswerSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // Test 2B: Error cases
  // -------------------------------------------------------------------------

  describe('Test 2B: Error cases', () => {
    it('should throw ANSWER_NOT_FOUND when DAO returns null', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await FinalizedAnswerExportService.getFinalizedAnswer(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_FOUND');
        expect((e as AnswerError).statusCode).toBe(404);
      }
    });

    it('should throw ANSWER_NOT_LOCKED when status != FINALIZED', async () => {
      mockDAO.findById.mockResolvedValue(completedUnlockedAnswer);

      try {
        await FinalizedAnswerExportService.getFinalizedAnswer(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_LOCKED');
        expect((e as AnswerError).statusCode).toBe(422);
      }
    });

    it('should throw ANSWER_NOT_LOCKED when finalized but locked=false', async () => {
      mockDAO.findById.mockResolvedValue(finalizedNotLockedAnswer);

      try {
        await FinalizedAnswerExportService.getFinalizedAnswer(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_LOCKED');
        expect((e as AnswerError).statusCode).toBe(422);
      }
    });
  });
});
