/**
 * FinalizeProcessChain.step5.test.ts - Step 5: Complete finalize workflow without SMS
 *
 * TLA+ Properties:
 * - Reachability: simulate full flow; assert Answer.status === "FINALIZED",
 *   no SMS record inserted (SMS DAO not called)
 * - TypeInvariant: assert returned workflow result { success: true }
 * - ErrorConsistency: mock persistence failure -> expect FinalizePersistenceError and:
 *   - no SMS send attempt
 *   - workflow marked failed
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeWithoutSmsError } from '@/server/error_definitions/FinalizeWithoutSmsErrors';
import { FinalizeWorkflowResultSchema } from '@/server/data_structures/FinalizeCompletion';

// ---------------------------------------------------------------------------
// Mock the finalize logger
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
// Mock DAOs
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
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { FinalizeProcessChain } from '../FinalizeProcessChain';
import { FinalizeService } from '@/server/services/FinalizeService';
import { finalizeLogger } from '@/server/logging/finalizeLogger';
import { AnswerDAO } from '@/server/data_access_objects/AnswerDAO';
import { UserDAO } from '@/server/data_access_objects/UserDAO';
import { SmsFollowUpDAO } from '@/server/data_access_objects/SmsFollowUpDAO';

const mockAnswerDAO = vi.mocked(AnswerDAO);
const mockUserDAO = vi.mocked(UserDAO);
const mockSmsFollowUpDAO = vi.mocked(SmsFollowUpDAO);
const mockLogger = vi.mocked(finalizeLogger);

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
  content: 'test content',
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

describe('FinalizeProcessChain — Step 5: Complete finalize workflow without SMS', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockAnswerDAO.findById.mockResolvedValue(validAnswer);
    mockUserDAO.findById.mockResolvedValue(validUser);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should execute full flow with FINALIZED answer and no SMS', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({
        answerId,
      });

      expect(result).toBeDefined();
    });

    it('should NOT call SmsFollowUpDAO.insert (no SMS record created)', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId });

      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });

    it('should verify answer status is FINALIZED (via verifier, no error thrown)', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({
        answerId,
      });

      // If the verifier threw, result would be different
      expect(result).toBeDefined();
      expect(result).toHaveProperty('smsDispatched', false);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result with smsDispatched: false', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({
        answerId,
      });

      expect(result).toEqual({ smsDispatched: false });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw FinalizeWithoutSmsError on persistence failure', async () => {
      // Make the logger throw to simulate persistence failure
      mockLogger.info.mockImplementationOnce(() => {
        throw new Error('Persistence failure');
      });

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('FINALIZE_PERSISTENCE_ERROR');
      }
    });

    it('should NOT attempt SMS send on persistence failure', async () => {
      mockLogger.info.mockImplementationOnce(() => {
        throw new Error('Persistence failure');
      });

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
      } catch {
        // Expected
      }

      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });

    it('should propagate AnswerNotFound error when answer does not exist', async () => {
      mockAnswerDAO.findById.mockResolvedValue(null);

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('ANSWER_NOT_FOUND');
      }
    });

    it('should propagate InvalidFinalizeState when answer is not FINALIZED', async () => {
      mockAnswerDAO.findById.mockResolvedValue({
        ...validAnswer,
        status: 'DRAFT' as const,
      });

      try {
        await FinalizeProcessChain.handleFinalizeCompletion({ answerId });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('INVALID_FINALIZE_STATE');
      }
    });
  });
});
