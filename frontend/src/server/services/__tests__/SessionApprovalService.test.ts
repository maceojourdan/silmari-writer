/**
 * SessionApprovalService.test.ts - Step 3: Process Approval Request
 *
 * TLA+ Properties:
 * - Reachability: Mock DAO returning session { state: 'DRAFT' } → returns { newState: 'FINALIZE' }
 * - TypeInvariant: Returned object matches SessionTransitionResult type
 * - ErrorConsistency: DAO returns null → SessionNotFoundError;
 *                     DAO returns state FINALIZE → InvalidStateTransitionError
 *
 * Resource: db-h2s4 (service)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionTransitionResultSchema } from '@/server/data_structures/Session';
import { StateTransitionError } from '@/server/error_definitions/StateTransitionErrors';

// ---------------------------------------------------------------------------
// Mock DAO
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
  },
}));

import { SessionDAO } from '../../data_access_objects/SessionDAO';
import { SessionApprovalService } from '../SessionApprovalService';

const mockDAO = vi.mocked(SessionDAO);

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

describe('SessionApprovalService.approve — Step 3: Process Approval Request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return transition instruction { newState: FINALIZE } for DRAFT session', async () => {
      mockDAO.findById.mockResolvedValue(draftSession);

      const result = await SessionApprovalService.approve(sessionId);

      expect(result).toBeDefined();
      expect(result.newState).toBe('FINALIZE');
      expect(mockDAO.findById).toHaveBeenCalledWith(sessionId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching SessionTransitionResult schema', async () => {
      mockDAO.findById.mockResolvedValue(draftSession);

      const result = await SessionApprovalService.approve(sessionId);
      const parsed = SessionTransitionResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SessionNotFound when DAO returns null', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await SessionApprovalService.approve(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(StateTransitionError);
        expect((e as StateTransitionError).code).toBe('SESSION_NOT_FOUND');
        expect((e as StateTransitionError).statusCode).toBe(404);
      }
    });

    it('should throw InvalidStateTransition when session state is FINALIZE', async () => {
      mockDAO.findById.mockResolvedValue(finalizeSession);

      try {
        await SessionApprovalService.approve(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(StateTransitionError);
        expect((e as StateTransitionError).code).toBe('INVALID_STATE_TRANSITION');
        expect((e as StateTransitionError).statusCode).toBe(409);
      }
    });
  });
});
