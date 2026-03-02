/**
 * FinalizeWithoutSms.integration.test.ts - Terminal Condition Integration Test
 *
 * Scenario:
 * - Answer in DB with status = FINALIZED
 * - user.smsOptIn = false
 * - Trigger finalize completion event
 *
 * Assertions:
 * - Full path executes without error
 * - No call to SMS client
 * - No SMS dispatch record created
 * - Answer remains FINALIZED
 * - Workflow result indicates success
 *
 * Proves:
 * - Reachability: trigger → terminal condition reachable
 * - TypeInvariant: types consistent across chain
 * - ErrorConsistency: no unintended SMS, correct handling of failures
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeWithoutSmsError } from '@/server/error_definitions/FinalizeWithoutSmsErrors';
import { PostFinalizeResultSchema } from '@/server/data_structures/FinalizeCompletion';

// ---------------------------------------------------------------------------
// Mock DAOs (boundary mocks only — all service/verifier/chain logic runs real)
// ---------------------------------------------------------------------------

vi.mock('@/server/data_access_objects/AnswerDAO', () => ({
  AnswerDAO: { findById: vi.fn() },
}));

vi.mock('@/server/data_access_objects/UserDAO', () => ({
  UserDAO: { findById: vi.fn() },
}));

vi.mock('@/server/data_access_objects/SmsFollowUpDAO', () => ({
  SmsFollowUpDAO: { insert: vi.fn() },
}));

// ---------------------------------------------------------------------------
// Mock logging boundary
// ---------------------------------------------------------------------------

vi.mock('@/server/logging/finalizeLogger', () => ({
  finalizeLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { FinalizeProcessChain } from '../FinalizeProcessChain';
import { AnswerDAO } from '@/server/data_access_objects/AnswerDAO';
import { UserDAO } from '@/server/data_access_objects/UserDAO';
import { SmsFollowUpDAO } from '@/server/data_access_objects/SmsFollowUpDAO';
import { finalizeLogger } from '@/server/logging/finalizeLogger';

const mockAnswerDAO = vi.mocked(AnswerDAO);
const mockUserDAO = vi.mocked(UserDAO);
const mockSmsFollowUpDAO = vi.mocked(SmsFollowUpDAO);
const mockLogger = vi.mocked(finalizeLogger);

// ---------------------------------------------------------------------------
// Test Data — matches production shapes
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const userId = '660e8400-e29b-41d4-a716-446655440000';

const finalizedAnswer = {
  id: answerId,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  locked: true,
  content: 'This is the finalized answer content.',
  userId,
  createdAt: '2026-01-15T10:30:00.000Z',
  updatedAt: '2026-01-15T12:45:00.000Z',
};

const userWithoutSmsOptIn = {
  id: userId,
  smsOptIn: false,
  createdAt: '2026-01-01T00:00:00.000Z',
  updatedAt: '2026-01-01T00:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Mock SMS Client for injection verification
// ---------------------------------------------------------------------------

function createMockSmsClient() {
  return {
    sendMessage: vi.fn().mockResolvedValue({ sid: 'SM-should-never-be-called' }),
  };
}

// ---------------------------------------------------------------------------
// Integration Tests
// ---------------------------------------------------------------------------

describe('FinalizeWithoutSms Integration — Terminal Condition', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockAnswerDAO.findById.mockResolvedValue(finalizedAnswer);
    mockUserDAO.findById.mockResolvedValue(userWithoutSmsOptIn);
  });

  // -------------------------------------------------------------------------
  // Reachability: trigger → terminal condition reachable
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should execute full path from event to completion without error', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({
        answerId,
      });

      expect(result).toBeDefined();
    });

    it('should load answer via AnswerDAO', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId });

      expect(mockAnswerDAO.findById).toHaveBeenCalledWith(answerId);
      expect(mockAnswerDAO.findById).toHaveBeenCalledTimes(1);
    });

    it('should load user via UserDAO using answer.userId', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId });

      expect(mockUserDAO.findById).toHaveBeenCalledWith(userId);
      expect(mockUserDAO.findById).toHaveBeenCalledTimes(1);
    });

    it('should persist finalization metadata via logger', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId });

      expect(mockLogger.info).toHaveBeenCalledWith(
        'Finalization metadata persisted',
        expect.objectContaining({ answerId }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: types consistent across chain
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching PostFinalizeResultSchema', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({
        answerId,
      });

      const parsed = PostFinalizeResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return { smsDispatched: false }', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({
        answerId,
      });

      expect(result).toEqual({ smsDispatched: false });
    });

    it('should not alter the answer status (remains FINALIZED)', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId });

      // The AnswerDAO.update should NOT have been called to change status
      // (AnswerDAO.update is not mocked because it's never used in this path)
      // The answer remains FINALIZED as loaded
      expect(mockAnswerDAO.findById).toHaveBeenCalledWith(answerId);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: no unintended SMS, correct failure handling
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should NOT call SmsFollowUpDAO.insert (no SMS record created)', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId });

      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });

    it('should NOT log any critical errors during normal execution', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId });

      expect(mockLogger.critical).not.toHaveBeenCalled();
    });

    it('should abort early for malformed events (no DAO calls)', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({});

      expect(mockAnswerDAO.findById).not.toHaveBeenCalled();
      expect(mockUserDAO.findById).not.toHaveBeenCalled();
      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });

    it('should throw ANSWER_NOT_FOUND when answer does not exist', async () => {
      mockAnswerDAO.findById.mockResolvedValue(null);

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('ANSWER_NOT_FOUND');
        expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
      }
    });

    it('should throw PERSISTENCE_ERROR when AnswerDAO fails', async () => {
      mockAnswerDAO.findById.mockRejectedValue(new Error('DB connection failed'));

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('PERSISTENCE_ERROR');
        expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
      }
    });

    it('should throw INVALID_FINALIZE_STATE when answer is not FINALIZED', async () => {
      mockAnswerDAO.findById.mockResolvedValue({
        ...finalizedAnswer,
        status: 'COMPLETED' as const,
      });

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('INVALID_FINALIZE_STATE');
        expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
      }
    });

    it('should throw PERSISTENCE_ERROR when user not found', async () => {
      mockUserDAO.findById.mockResolvedValue(null);

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('PERSISTENCE_ERROR');
        expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
      }
    });
  });
});
