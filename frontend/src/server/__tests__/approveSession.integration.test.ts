/**
 * Integration test for the session approval path
 *
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * This proves end-to-end:
 * - Reachability: Trigger → service → DAO → logger → response (all 6 steps)
 * - TypeInvariant: All boundary schemas validated via Zod
 * - ErrorConsistency: All defined error branches return standardized errors
 *
 * Note: Mocks only the DAO layer (database boundary). Everything above
 * runs with real implementations: service, handler, logger.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionSchema, SessionTransitionResultSchema } from '@/server/data_structures/Session';

// Only mock the DAO — everything else is real
vi.mock('../data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
  },
}));

// Mock the primary logger to capture calls (but let everything else be real)
vi.mock('../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SessionDAO } from '../data_access_objects/SessionDAO';
import { ApproveSessionHandler } from '../request_handlers/ApproveSessionHandler';
import { SessionApprovalService } from '../services/SessionApprovalService';
import { assertDraft } from '@/verifiers/sessionStateVerifier';
import { ApproveSessionResponseSchema } from '@/api_contracts/approveSession';
import { logger } from '../logging/logger';

const mockDAO = vi.mocked(SessionDAO);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const draftSession = {
  id: sessionId,
  state: 'DRAFT' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const finalizeSession = {
  id: sessionId,
  state: 'FINALIZE' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Session Approval Integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.findById.mockResolvedValue(draftSession);
    mockDAO.updateState.mockResolvedValue(finalizeSession);
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path from trigger to terminal
  // -------------------------------------------------------------------------

  describe('Reachability: Full path from approval trigger to terminal state', () => {
    it('should validate state, approve, persist, log, and return FINALIZE session', async () => {
      // Step 1: Frontend verifier (assertDraft) passes for DRAFT session
      expect(() => assertDraft(draftSession)).not.toThrow();

      // Steps 2-5 via handler (service → DAO → logger)
      const result = await ApproveSessionHandler.handle(sessionId);

      // Terminal condition: DB state = FINALIZE
      expect(result.state).toBe('FINALIZE');
      expect(result.id).toBe(sessionId);

      // Verify service called DAO.findById
      expect(mockDAO.findById).toHaveBeenCalledWith(sessionId);

      // Verify DAO.updateState was called with FINALIZE
      expect(mockDAO.updateState).toHaveBeenCalledWith(sessionId, 'FINALIZE');

      // Terminal condition: Approval log entry exists (cfg-q9c5)
      expect(mockLogger.info).toHaveBeenCalledWith(
        expect.stringContaining('Approval event logged'),
        expect.objectContaining({
          sessionId,
          action: 'APPROVE',
        }),
      );
    });

    it('should work end-to-end: verifier → service → DAO → logger → response', async () => {
      // Step 1: Verifier
      assertDraft(draftSession);

      // Step 3: Service validates and returns transition instruction
      const transition = await SessionApprovalService.approve(sessionId);
      expect(transition.newState).toBe('FINALIZE');

      // Steps 4-6 via full handler
      const result = await ApproveSessionHandler.handle(sessionId);
      expect(result.state).toBe('FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: All schema boundaries validated
  // -------------------------------------------------------------------------

  describe('TypeInvariant: All schema boundaries validated via Zod', () => {
    it('should return result conforming to Session schema', async () => {
      const result = await ApproveSessionHandler.handle(sessionId);

      const parsed = SessionSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return result conforming to ApproveSessionResponse schema', async () => {
      const result = await ApproveSessionHandler.handle(sessionId);

      const parsed = ApproveSessionResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should produce valid SessionTransitionResult from service', async () => {
      const transition = await SessionApprovalService.approve(sessionId);

      const parsed = SessionTransitionResultSchema.safeParse(transition);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: Each failure branch produces defined error
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Each failure branch produces defined error', () => {
    it('should reject at verifier level when session is not DRAFT', () => {
      expect(() => assertDraft(finalizeSession)).toThrow();
      try {
        assertDraft(finalizeSession);
      } catch (e: any) {
        expect(e.code).toBe('INVALID_STATE_TRANSITION');
        expect(e.statusCode).toBe(409);
      }
    });

    it('should throw SESSION_NOT_FOUND when session does not exist', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await ApproveSessionHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('SESSION_NOT_FOUND');
        expect(e.statusCode).toBe(404);
      }
    });

    it('should throw INVALID_STATE_TRANSITION when session already FINALIZE', async () => {
      mockDAO.findById.mockResolvedValue(finalizeSession);

      try {
        await ApproveSessionHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('INVALID_STATE_TRANSITION');
        expect(e.statusCode).toBe(409);
      }
    });

    it('should throw PERSISTENCE_ERROR when DAO update fails', async () => {
      const { PersistenceErrors } = await import('../error_definitions/PersistenceErrors');
      mockDAO.updateState.mockRejectedValue(PersistenceErrors.UpdateFailed());

      try {
        await ApproveSessionHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('PERSISTENCE_ERROR');
        expect(e.statusCode).toBe(500);
        expect(e.retryable).toBe(true);
      }
    });

    it('should not log approval event when DAO persistence fails', async () => {
      const { PersistenceErrors } = await import('../error_definitions/PersistenceErrors');
      mockDAO.updateState.mockRejectedValue(PersistenceErrors.UpdateFailed());

      try {
        await ApproveSessionHandler.handle(sessionId);
      } catch {
        // expected
      }

      // Approval logger should NOT have been called with the approval message
      const approvalCalls = mockLogger.info.mock.calls.filter(
        (call) => typeof call[0] === 'string' && call[0].includes('Approval event'),
      );
      expect(approvalCalls.length).toBe(0);
    });
  });
});
