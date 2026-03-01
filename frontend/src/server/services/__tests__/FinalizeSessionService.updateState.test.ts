/**
 * FinalizeSessionService.updateState.test.ts - Step 3: Update session state to FINALIZE
 *
 * TLA+ Properties:
 * - Reachability: Given validated session, DAO updateSessionState resolves → session.state === "FINALIZE"
 * - TypeInvariant: Persisted entity calls DAO with state "FINALIZE"
 * - ErrorConsistency: DAO throws → SessionPersistenceError; StoryRecord DAO not called
 *
 * Resource: db-h2s4 (service)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock only the DAO
vi.mock('../../data_access_objects/SessionStoryRecordDAO', () => ({
  SessionStoryRecordDAO: {
    findSessionById: vi.fn(),
    updateSessionState: vi.fn(),
    upsertStoryRecord: vi.fn(),
  },
}));

import { SessionStoryRecordDAO } from '../../data_access_objects/SessionStoryRecordDAO';
import { FinalizeSessionService } from '../FinalizeSessionService';

const mockDAO = vi.mocked(SessionStoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const updatedSession = {
  id: sessionId,
  state: 'FINALIZE' as const,
  requiredInputsComplete: true,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeSessionService.updateState — Step 3: Update session state to FINALIZE', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DAO.updateSessionState with FINALIZE', async () => {
      mockDAO.updateSessionState.mockResolvedValue(updatedSession);

      await FinalizeSessionService.updateState(sessionId);

      expect(mockDAO.updateSessionState).toHaveBeenCalledWith(sessionId, 'FINALIZE');
    });

    it('should resolve without error on success', async () => {
      mockDAO.updateSessionState.mockResolvedValue(updatedSession);

      await expect(FinalizeSessionService.updateState(sessionId)).resolves.toBeUndefined();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass state enum value FINALIZE to DAO', async () => {
      mockDAO.updateSessionState.mockResolvedValue(updatedSession);

      await FinalizeSessionService.updateState(sessionId);

      const [, stateArg] = mockDAO.updateSessionState.mock.calls[0];
      expect(stateArg).toBe('FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SESSION_PERSISTENCE_ERROR when DAO fails', async () => {
      mockDAO.updateSessionState.mockRejectedValue(new Error('Connection refused'));

      try {
        await FinalizeSessionService.updateState(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('SESSION_PERSISTENCE_ERROR');
        expect((e as { statusCode: number }).statusCode).toBe(500);
        expect((e as { retryable: boolean }).retryable).toBe(true);
      }
    });

    it('should NOT call upsertStoryRecord when state update fails', async () => {
      mockDAO.updateSessionState.mockRejectedValue(new Error('DB error'));

      try {
        await FinalizeSessionService.updateState(sessionId);
      } catch {
        // expected
      }

      expect(mockDAO.upsertStoryRecord).not.toHaveBeenCalled();
    });
  });
});
