/**
 * SessionInitializationService Story Tests - Step 5: Service creates StoryRecord in INIT status
 *
 * Resource: db-h2s4 (service)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * TLA+ properties tested:
 * - Reachability: Mock DAO createSession + createStory success → story.status === 'INIT', story.sessionId === session.id
 * - TypeInvariant: StoryRecord matches AnswerStoryRecord schema
 * - ErrorConsistency: Story creation failure → STORY_PERSISTENCE_ERROR + session rolled back
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
import { AnswerStoryRecordSchema } from '@/server/data_structures/AnswerSession';
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

describe('SessionInitializationService — Step 5: Service creates StoryRecord in INIT status', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should create StoryRecord with status INIT', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockResolvedValue(mockStoryRecord);

      const result = await SessionInitializationService.initializeSession('user-abc12345');

      expect(mockDAO.createStoryRecord).toHaveBeenCalledWith(mockAnswerSession.id);
      expect(result.storyRecordId).toBe(mockStoryRecord.id);
    });

    it('should link story.sessionId to session.id', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockResolvedValue(mockStoryRecord);

      await SessionInitializationService.initializeSession('user-abc12345');

      // Verify createStoryRecord was called with the session's ID
      expect(mockDAO.createStoryRecord).toHaveBeenCalledWith(mockAnswerSession.id);

      // Verify returned storyRecord matches
      const storyRecord = await mockDAO.createStoryRecord.mock.results[0].value;
      expect(storyRecord.sessionId).toBe(mockAnswerSession.id);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should create a StoryRecord that conforms to AnswerStoryRecord schema', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockResolvedValue(mockStoryRecord);

      await SessionInitializationService.initializeSession('user-abc12345');

      const storyRecord = await mockDAO.createStoryRecord.mock.results[0].value;
      const validation = AnswerStoryRecordSchema.safeParse(storyRecord);
      expect(validation.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw STORY_PERSISTENCE_ERROR when createStoryRecord fails', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockRejectedValue(new Error('Story table not found'));

      await expect(
        SessionInitializationService.initializeSession('user-abc12345'),
      ).rejects.toThrow(SessionError);

      // Reset mocks for second call
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockRejectedValue(new Error('Story table not found'));

      await expect(
        SessionInitializationService.initializeSession('user-abc12345'),
      ).rejects.toMatchObject({
        code: 'STORY_PERSISTENCE_ERROR',
      });
    });

    it('should rollback session when story creation fails (deleteSession called)', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockRejectedValue(new Error('Story table not found'));
      mockDAO.deleteSession.mockResolvedValue(undefined);

      try {
        await SessionInitializationService.initializeSession('user-abc12345');
      } catch {
        // Expected to throw
      }

      expect(mockDAO.deleteSession).toHaveBeenCalledWith(mockAnswerSession.id);
    });

    it('should still throw STORY_PERSISTENCE_ERROR even if rollback fails', async () => {
      mockDAO.createSession.mockResolvedValue(mockAnswerSession);
      mockDAO.createStoryRecord.mockRejectedValue(new Error('Story table not found'));
      mockDAO.deleteSession.mockRejectedValue(new Error('Rollback also failed'));

      await expect(
        SessionInitializationService.initializeSession('user-abc12345'),
      ).rejects.toMatchObject({
        code: 'STORY_PERSISTENCE_ERROR',
      });
    });
  });
});
