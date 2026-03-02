/**
 * step2-load-data.test.ts - Step 2: Load Answer and Contact Data
 *
 * TLA+ Properties:
 * - Reachability: Given valid IDs, both DAOs return data → structured payload with answerSummary and phoneNumber
 * - TypeInvariant: Payload passes SmsPayloadSchema.safeParse()
 * - ErrorConsistency (answer null): AnswerDAO returns null → SmsError ANSWER_NOT_FOUND
 * - ErrorConsistency (answer throw): AnswerDAO throws Error → SmsError DATABASE_FAILURE
 * - ErrorConsistency (user null): UserDAO returns null → SmsError DATABASE_FAILURE
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SmsPayloadSchema } from '@/server/data_structures/FinalizeEvent';
import { SmsError } from '@/server/error_definitions/SmsErrors';

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
import { TriggerSmsFollowUpService } from '../TriggerSmsFollowUpService';

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
  locked: false,
  content: 'My finalized answer content',
  userId,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const validUser = {
  id: userId,
  smsOptIn: true,
  phoneNumber: '+15551234567',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TriggerSmsFollowUpService.loadAnswerAndContact — Step 2: Load Answer and Contact Data', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return structured payload with answerSummary and phoneNumber when both DAOs return data', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);

      const result = await TriggerSmsFollowUpService.loadAnswerAndContact(answerId, userId);

      expect(mockAnswerDAO.findById).toHaveBeenCalledWith(answerId);
      expect(mockUserDAO.findById).toHaveBeenCalledWith(userId);
      expect(result).toHaveProperty('answerSummary');
      expect(result).toHaveProperty('phoneNumber');
      expect(result.phoneNumber).toBe('+15551234567');
      expect(typeof result.answerSummary).toBe('string');
      expect(result.answerSummary.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object passing SmsPayloadSchema validation', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);

      const result = await TriggerSmsFollowUpService.loadAnswerAndContact(answerId, userId);
      const parsed = SmsPayloadSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SmsError with code ANSWER_NOT_FOUND when AnswerDAO returns null', async () => {
      mockAnswerDAO.findById.mockResolvedValue(null);
      mockUserDAO.findById.mockResolvedValue(validUser);

      try {
        await TriggerSmsFollowUpService.loadAnswerAndContact(answerId, userId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('ANSWER_NOT_FOUND');
      }
    });

    it('should throw SmsError with code DATABASE_FAILURE when AnswerDAO throws Error', async () => {
      mockAnswerDAO.findById.mockRejectedValue(new Error('DB connection lost'));
      mockUserDAO.findById.mockResolvedValue(validUser);

      try {
        await TriggerSmsFollowUpService.loadAnswerAndContact(answerId, userId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('DATABASE_FAILURE');
      }
    });

    it('should throw SmsError with code DATABASE_FAILURE when UserDAO returns null', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(null);

      try {
        await TriggerSmsFollowUpService.loadAnswerAndContact(answerId, userId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('DATABASE_FAILURE');
      }
    });
  });
});
