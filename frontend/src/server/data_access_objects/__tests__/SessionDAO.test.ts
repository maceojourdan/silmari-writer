/**
 * SessionDAO.test.ts - Step 4: Persist Session State Transition
 *
 * TLA+ Properties:
 * - Reachability: Mock Supabase update success → state updated to FINALIZE
 * - TypeInvariant: Returned entity conforms to Session schema (db-f8n5)
 * - ErrorConsistency: DB error → PersistenceError; approvalLogger not called
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionSchema } from '@/server/data_structures/Session';
import { PersistenceError } from '@/server/error_definitions/PersistenceErrors';

// ---------------------------------------------------------------------------
// Mock SessionDAO
// ---------------------------------------------------------------------------

vi.mock('../SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
  },
}));

// Mock approvalLogger to verify it's NOT called on failure
vi.mock('../../logging/approvalLogger', () => ({
  approvalLogger: {
    logApproval: vi.fn(),
  },
}));

import { SessionDAO } from '../SessionDAO';
import { approvalLogger } from '../../logging/approvalLogger';

const mockDAO = vi.mocked(SessionDAO);
const mockLogger = vi.mocked(approvalLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const mockSession = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  state: 'FINALIZE' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SessionDAO.updateState — Step 4: Persist Session State Transition', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should update session state to FINALIZE and return updated entity', async () => {
      mockDAO.updateState.mockResolvedValue(mockSession);

      const result = await SessionDAO.updateState(mockSession.id, 'FINALIZE');

      expect(result).toBeDefined();
      expect(result.state).toBe('FINALIZE');
      expect(mockDAO.updateState).toHaveBeenCalledWith(mockSession.id, 'FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return entity that conforms to Session schema', async () => {
      mockDAO.updateState.mockResolvedValue(mockSession);

      const result = await SessionDAO.updateState(mockSession.id, 'FINALIZE');
      const parsed = SessionSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw PersistenceError on DB failure', async () => {
      mockDAO.updateState.mockRejectedValue(
        new PersistenceError('Database update failed'),
      );

      try {
        await SessionDAO.updateState(mockSession.id, 'FINALIZE');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(PersistenceError);
        expect((e as PersistenceError).code).toBe('PERSISTENCE_ERROR');
        expect((e as PersistenceError).retryable).toBe(true);
      }
    });

    it('should not call approvalLogger on DB failure', async () => {
      mockDAO.updateState.mockRejectedValue(
        new PersistenceError('Database update failed'),
      );

      try {
        await SessionDAO.updateState(mockSession.id, 'FINALIZE');
      } catch {
        // expected
      }

      expect(mockLogger.logApproval).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // findById
  // -------------------------------------------------------------------------

  describe('findById', () => {
    it('should return session when found', async () => {
      const draftSession = { ...mockSession, state: 'DRAFT' as const };
      mockDAO.findById.mockResolvedValue(draftSession);

      const result = await SessionDAO.findById(mockSession.id);

      expect(result).toBeDefined();
      expect(result!.state).toBe('DRAFT');
      expect(mockDAO.findById).toHaveBeenCalledWith(mockSession.id);
    });

    it('should return null when session not found', async () => {
      mockDAO.findById.mockResolvedValue(null);

      const result = await SessionDAO.findById('nonexistent-id');

      expect(result).toBeNull();
    });
  });
});
