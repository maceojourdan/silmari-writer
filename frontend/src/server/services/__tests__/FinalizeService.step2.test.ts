/**
 * FinalizeService.step2.test.ts - Step 2: Load Answer With User Preference
 *
 * TLA+ Properties:
 * - Reachability: Given valid answerId, both DAOs return data -> enriched entity { id, status, user: { smsOptIn } }
 * - TypeInvariant: Returned object passes AnswerWithUserPreferenceSchema.safeParse()
 * - ErrorConsistency (answer null): AnswerDAO returns null -> FinalizeWithoutSmsError ANSWER_NOT_FOUND
 * - ErrorConsistency (answer throw): AnswerDAO throws Error -> FinalizeWithoutSmsError PERSISTENCE_ERROR
 * - ErrorConsistency (user null): UserDAO returns null -> FinalizeWithoutSmsError PERSISTENCE_ERROR
 * - ErrorConsistency (user throw): UserDAO throws Error -> FinalizeWithoutSmsError PERSISTENCE_ERROR
 *
 * Resource: db-h2s4 (service)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AnswerWithUserPreferenceSchema } from '@/server/data_structures/FinalizeCompletion';
import { FinalizeWithoutSmsError } from '@/server/error_definitions/FinalizeWithoutSmsErrors';

// ---------------------------------------------------------------------------
// Mock DAOs
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/AnswerDAO', () => ({
  AnswerDAO: {
    findById: vi.fn(),
  },
}));

vi.mock('../../data_access_objects/UserDAO', () => ({
  UserDAO: {
    findById: vi.fn(),
  },
}));

import { AnswerDAO } from '../../data_access_objects/AnswerDAO';
import { UserDAO } from '../../data_access_objects/UserDAO';
import { FinalizeService } from '../FinalizeService';

const mockAnswerDAO = vi.mocked(AnswerDAO);
const mockUserDAO = vi.mocked(UserDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const userId = '660e8400-e29b-41d4-a716-446655440000';

const validAnswer = {
  id: answerId,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  locked: true,
  content: 'test',
  userId,
  createdAt: '2026-01-01T00:00:00.000Z',
  updatedAt: '2026-01-01T00:00:00.000Z',
};

const validUser = {
  id: userId,
  smsOptIn: false,
  createdAt: '2026-01-01T00:00:00.000Z',
  updatedAt: '2026-01-01T00:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeService.loadAnswerWithPreference — Step 2: Load Answer With User Preference', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return enriched entity with id, status, and user.smsOptIn when both DAOs return data', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);

      const result = await FinalizeService.loadAnswerWithPreference(answerId);

      expect(mockAnswerDAO.findById).toHaveBeenCalledWith(answerId);
      expect(mockUserDAO.findById).toHaveBeenCalledWith(userId);
      expect(result).toEqual({
        id: answerId,
        status: 'FINALIZED',
        user: { smsOptIn: false },
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object passing AnswerWithUserPreferenceSchema validation', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);

      const result = await FinalizeService.loadAnswerWithPreference(answerId);
      const parsed = AnswerWithUserPreferenceSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw FinalizeWithoutSmsError with code ANSWER_NOT_FOUND when AnswerDAO returns null', async () => {
      mockAnswerDAO.findById.mockResolvedValue(null);

      try {
        await FinalizeService.loadAnswerWithPreference(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('ANSWER_NOT_FOUND');
      }
    });

    it('should throw FinalizeWithoutSmsError with code PERSISTENCE_ERROR when AnswerDAO throws', async () => {
      mockAnswerDAO.findById.mockRejectedValue(new Error('DB connection lost'));

      try {
        await FinalizeService.loadAnswerWithPreference(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('PERSISTENCE_ERROR');
      }
    });

    it('should throw FinalizeWithoutSmsError with code PERSISTENCE_ERROR when UserDAO returns null', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(null);

      try {
        await FinalizeService.loadAnswerWithPreference(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('PERSISTENCE_ERROR');
      }
    });

    it('should throw FinalizeWithoutSmsError with code PERSISTENCE_ERROR when UserDAO throws', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockRejectedValue(new Error('DB timeout'));

      try {
        await FinalizeService.loadAnswerWithPreference(answerId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('PERSISTENCE_ERROR');
      }
    });
  });
});
