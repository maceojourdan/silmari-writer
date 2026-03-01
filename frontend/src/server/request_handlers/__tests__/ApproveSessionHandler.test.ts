/**
 * ApproveSessionHandler.test.ts - Tests for the session approval request handler
 *
 * TLA+ Properties:
 * - Reachability: Service approves → DAO updates → logger logs → returns updated session
 * - TypeInvariant: Returned session matches Session schema
 * - ErrorConsistency: StateTransitionError and PersistenceError rethrown as-is;
 *                     unknown errors wrapped in GenericError
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionSchema } from '@/server/data_structures/Session';
import { StateTransitionError } from '@/server/error_definitions/StateTransitionErrors';
import { PersistenceError } from '@/server/error_definitions/PersistenceErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../services/SessionApprovalService', () => ({
  SessionApprovalService: {
    approve: vi.fn(),
  },
}));

vi.mock('../../data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
  },
}));

vi.mock('../../logging/approvalLogger', () => ({
  approvalLogger: {
    logApproval: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ApproveSessionHandler } from '../ApproveSessionHandler';
import { SessionApprovalService } from '../../services/SessionApprovalService';
import { SessionDAO } from '../../data_access_objects/SessionDAO';
import { approvalLogger } from '../../logging/approvalLogger';

const mockService = vi.mocked(SessionApprovalService);
const mockDAO = vi.mocked(SessionDAO);
const mockLogger = vi.mocked(approvalLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const updatedSession = {
  id: sessionId,
  state: 'FINALIZE' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

const logEntry = {
  sessionId,
  action: 'APPROVE' as const,
  timestamp: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ApproveSessionHandler — Full request flow', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockService.approve.mockResolvedValue({ newState: 'FINALIZE' });
    mockDAO.updateState.mockResolvedValue(updatedSession);
    mockLogger.logApproval.mockResolvedValue(logEntry);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call service → DAO → logger and return updated session', async () => {
      const result = await ApproveSessionHandler.handle(sessionId);

      expect(mockService.approve).toHaveBeenCalledWith(sessionId);
      expect(mockDAO.updateState).toHaveBeenCalledWith(sessionId, 'FINALIZE');
      expect(mockLogger.logApproval).toHaveBeenCalledWith(sessionId);
      expect(result).toEqual(updatedSession);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return session conforming to Session schema', async () => {
      const result = await ApproveSessionHandler.handle(sessionId);
      const parsed = SessionSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow StateTransitionError as-is', async () => {
      const error = new StateTransitionError('Not found', 'SESSION_NOT_FOUND', 404);
      mockService.approve.mockRejectedValue(error);

      try {
        await ApproveSessionHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(StateTransitionError);
        expect((e as StateTransitionError).code).toBe('SESSION_NOT_FOUND');
        expect((e as StateTransitionError).statusCode).toBe(404);
      }
    });

    it('should rethrow PersistenceError as-is', async () => {
      const error = new PersistenceError('DB failed');
      mockDAO.updateState.mockRejectedValue(error);

      try {
        await ApproveSessionHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(PersistenceError);
        expect((e as PersistenceError).code).toBe('PERSISTENCE_ERROR');
      }
    });

    it('should wrap unknown errors in GenericError', async () => {
      mockService.approve.mockRejectedValue(new Error('Something unexpected'));

      try {
        await ApproveSessionHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }
    });
  });
});
