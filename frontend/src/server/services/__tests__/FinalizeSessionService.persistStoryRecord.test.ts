/**
 * FinalizeSessionService.persistStoryRecord.test.ts - Step 4: Persist StoryRecord
 *
 * TLA+ Properties:
 * - Reachability: Session in FINALIZE state, DAO upsertStoryRecord resolves → StoryRecord.status === "FINALIZED"
 * - TypeInvariant: Returned object conforms to StoryRecord type
 * - ErrorConsistency: upsertStoryRecord throws → transaction rolls back (session state remains ACTIVE);
 *   StoryRecordPersistenceError thrown
 *
 * Resource: db-h2s4 (service)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock dependencies
vi.mock('../../data_access_objects/SessionStoryRecordDAO', () => ({
  SessionStoryRecordDAO: {
    findSessionById: vi.fn(),
    updateSessionState: vi.fn(),
    upsertStoryRecord: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SessionStoryRecordDAO } from '../../data_access_objects/SessionStoryRecordDAO';
import { FinalizeSessionService } from '../FinalizeSessionService';
import { logger } from '../../logging/logger';

const mockDAO = vi.mocked(SessionStoryRecordDAO);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';
const responses = ['Response 1 about leadership', 'Response 2 about challenges'];

const persistedStoryRecord = {
  id: '660e8400-e29b-41d4-a716-446655440001',
  draftId: 'draft-001',
  resumeId: 'resume-001',
  jobId: 'job-001',
  questionId: 'question-001',
  voiceSessionId: sessionId,
  userId: 'user-abc12345',
  status: 'FINALIZED' as const,
  content: 'Response 1 about leadership\n\nResponse 2 about challenges',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeSessionService.persistStoryRecord — Step 4: Persist StoryRecord', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DAO.upsertStoryRecord with sessionId, responses, and FINALIZED', async () => {
      mockDAO.upsertStoryRecord.mockResolvedValue(persistedStoryRecord);

      await FinalizeSessionService.persistStoryRecord(sessionId, responses);

      expect(mockDAO.upsertStoryRecord).toHaveBeenCalledWith(
        sessionId,
        responses,
        'FINALIZED',
      );
    });

    it('should return StoryRecord with status FINALIZED', async () => {
      mockDAO.upsertStoryRecord.mockResolvedValue(persistedStoryRecord);

      const result = await FinalizeSessionService.persistStoryRecord(sessionId, responses);

      expect(result.status).toBe('FINALIZED');
    });

    it('should return responses saved in content', async () => {
      mockDAO.upsertStoryRecord.mockResolvedValue(persistedStoryRecord);

      const result = await FinalizeSessionService.persistStoryRecord(sessionId, responses);

      expect(result.content).toContain('Response 1');
      expect(result.content).toContain('Response 2');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object conforming to StoryRecord type', async () => {
      mockDAO.upsertStoryRecord.mockResolvedValue(persistedStoryRecord);

      const result = await FinalizeSessionService.persistStoryRecord(sessionId, responses);

      expect(result).toHaveProperty('id');
      expect(result).toHaveProperty('status');
      expect(result).toHaveProperty('content');
      expect(result).toHaveProperty('userId');
      expect(typeof result.status).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw STORY_RECORD_PERSISTENCE_ERROR when upsertStoryRecord fails', async () => {
      mockDAO.upsertStoryRecord.mockRejectedValue(new Error('Write failed'));

      // Rollback should succeed
      mockDAO.updateSessionState.mockResolvedValue({
        id: sessionId,
        state: 'ACTIVE',
        createdAt: '2026-02-28T12:00:00.000Z',
        updatedAt: '2026-02-28T12:01:00.000Z',
      });

      try {
        await FinalizeSessionService.persistStoryRecord(sessionId, responses);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('STORY_RECORD_PERSISTENCE_ERROR');
        expect((e as { statusCode: number }).statusCode).toBe(500);
        expect((e as { retryable: boolean }).retryable).toBe(true);
      }
    });

    it('should rollback session state to ACTIVE on StoryRecord failure', async () => {
      mockDAO.upsertStoryRecord.mockRejectedValue(new Error('Write failed'));
      mockDAO.updateSessionState.mockResolvedValue({
        id: sessionId,
        state: 'ACTIVE',
        createdAt: '2026-02-28T12:00:00.000Z',
        updatedAt: '2026-02-28T12:01:00.000Z',
      });

      try {
        await FinalizeSessionService.persistStoryRecord(sessionId, responses);
      } catch {
        // expected
      }

      expect(mockDAO.updateSessionState).toHaveBeenCalledWith(sessionId, 'ACTIVE');
    });

    it('should still throw STORY_RECORD_PERSISTENCE_ERROR even if rollback fails', async () => {
      mockDAO.upsertStoryRecord.mockRejectedValue(new Error('Write failed'));
      mockDAO.updateSessionState.mockRejectedValue(new Error('Rollback also failed'));

      try {
        await FinalizeSessionService.persistStoryRecord(sessionId, responses);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('STORY_RECORD_PERSISTENCE_ERROR');
      }

      // Rollback failure should be logged
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('rollback'),
        expect.any(Error),
        expect.objectContaining({ path: '308-finalize-voice-session-and-persist-storyrecord' }),
      );
    });
  });
});
