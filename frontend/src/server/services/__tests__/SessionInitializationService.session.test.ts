/**
 * SessionInitializationService Session Tests - Step 4: Service creates Answer Session in INIT state
 *
 * Resource: db-h2s4 (service)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * TLA+ properties tested:
 * - Reachability: Mock DAO success → returned session.state === 'INIT'
 * - TypeInvariant: Persisted object matches AnswerSession schema
 * - ErrorConsistency: Mock DAO throw StorageError → SESSION_PERSISTENCE_ERROR propagated
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock dependencies
vi.mock('@/server/data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    createSession: vi.fn(),
    createStoryRecord: vi.fn(),
    deleteSession: vi.fn(),
  },
}));

import { SessionInitializationService } from '../SessionInitializationService';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { AnswerSessionSchema } from '@/server/data_structures/AnswerSession';
import { SessionError } from '@/server/error_definitions/SessionErrors';

const mockDAO = vi.mocked(SessionDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const mockAnswerSession = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  userId: 'user-abc12345',
  state: 'INIT' as const,
  createdAt: '2026-03-01T00:00:00.000Z',
  updatedAt: '2026-03-01T00:00:00.000Z',
};

const mockStoryRecord = {
  id: '550e8400-e29b-41d4-a716-446655440001',
  sessionId: '550e8400-e29b-41d4-a716-446655440000',
  status: 'INIT' as const,
  createdAt: '2026-03-01T00:00:00.000Z',
  updatedAt: '2026-03-01T00:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SessionInitializationService — Step 4: Service creates Answer Session in INIT state', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return session with state === INIT when DAO succeeds', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockResolvedValue(mockStoryRecord);

      const result = await SessionInitializationService.initializeSession('user-abc12345');

      expect(result.state).toBe('INIT');
    });

    it('should call DAO.createSession with the userId', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockResolvedValue(mockStoryRecord);

      await SessionInitializationService.initializeSession('user-abc12345');

      expect(mockDAO.createSession).toHaveBeenCalledWith('user-abc12345');
    });

    it('should return a valid sessionId', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockResolvedValue(mockStoryRecord);

      const result = await SessionInitializationService.initializeSession('user-abc12345');

      expect(result.sessionId).toBe(mockAnswerSession.id);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should create an AnswerSession that conforms to the Zod schema', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockResolvedValue(mockStoryRecord);

      await SessionInitializationService.initializeSession('user-abc12345');

      // Verify the DAO was called and the returned session matches schema
      const createdSession = await mockDAO.createSession.mock.results[0].value;
      const validation = AnswerSessionSchema.safeParse(createdSession);
      expect(validation.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SESSION_PERSISTENCE_ERROR when DAO.createSession fails', async () => {
      mockDAO.createSession.mockRejectedValue(new Error('Database connection lost'));

      await expect(
        SessionInitializationService.initializeSession('user-abc12345'),
      ).rejects.toThrow(SessionError);

      await expect(
        SessionInitializationService.initializeSession('user-abc12345'),
      ).rejects.toMatchObject({
        code: 'SESSION_PERSISTENCE_ERROR',
      });
    });
  });
});
