/**
 * Integration test for the session finalization path
 *
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 *
 * This proves end-to-end:
 * - Reachability: Trigger → Handler → Service → DAO → Response (all 6 steps → terminal condition)
 * - TypeInvariant: Types preserved across UI → API → Service → DB → Response
 * - ErrorConsistency: Each failure path returns defined error without partial updates
 *
 * Note: Mocks only the DAO layer (database boundary). Everything above
 * runs with real implementations: service, handler.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Only mock the DAO — everything else is real
vi.mock('../data_access_objects/SessionStoryRecordDAO', () => ({
  SessionStoryRecordDAO: {
    findSessionById: vi.fn(),
    updateSessionState: vi.fn(),
    upsertStoryRecord: vi.fn(),
  },
}));

vi.mock('../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SessionStoryRecordDAO } from '../data_access_objects/SessionStoryRecordDAO';
import { FinalizeSessionRequestHandler } from '../request_handlers/FinalizeSessionRequestHandler';
import { FinalizeSessionResponseSchema } from '@/api_contracts/finalizeSession';

const mockDAO = vi.mocked(SessionStoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const activeSession = {
  id: sessionId,
  state: 'ACTIVE',
  requiredInputsComplete: true,
  responses: [
    'I led a team of 8 engineers to rebuild our payment processing system.',
    'The biggest challenge was migrating live traffic without downtime.',
  ],
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const finalizedSession = {
  id: sessionId,
  state: 'FINALIZE' as const,
  requiredInputsComplete: true,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

const finalizedStoryRecord = {
  id: '660e8400-e29b-41d4-a716-446655440001',
  draftId: 'draft-001',
  resumeId: 'resume-001',
  jobId: 'job-001',
  questionId: 'question-001',
  voiceSessionId: sessionId,
  userId: 'user-abc12345',
  status: 'FINALIZED' as const,
  content: 'I led a team of 8 engineers...\n\nThe biggest challenge was...',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Finalize Session Integration — Path 308', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default happy path setup
    mockDAO.findSessionById.mockResolvedValue(activeSession);
    mockDAO.updateSessionState.mockResolvedValue(finalizedSession);
    mockDAO.upsertStoryRecord.mockResolvedValue(finalizedStoryRecord);
  });

  // =========================================================================
  // Reachability: trigger → all 6 steps → terminal condition
  // =========================================================================

  describe('Reachability: Full path from trigger to terminal condition', () => {
    it('should validate, update state, persist StoryRecord, and return confirmation', async () => {
      const result = await FinalizeSessionRequestHandler.handle(sessionId);

      // Terminal condition assertions
      expect(result.sessionState).toBe('FINALIZE');
      expect(result.storyRecordStatus).toBe('FINALIZED');

      // Verify all DAO calls were made in correct order
      expect(mockDAO.findSessionById).toHaveBeenCalledWith(sessionId);
      expect(mockDAO.updateSessionState).toHaveBeenCalledWith(sessionId, 'FINALIZE');
      expect(mockDAO.upsertStoryRecord).toHaveBeenCalledWith(
        sessionId,
        activeSession.responses,
        'FINALIZED',
      );
    });

    it('should execute steps in correct order: validate → update → persist', async () => {
      const callOrder: string[] = [];

      mockDAO.findSessionById.mockImplementation(async () => {
        callOrder.push('findSessionById');
        return activeSession;
      });

      mockDAO.updateSessionState.mockImplementation(async () => {
        callOrder.push('updateSessionState');
        return finalizedSession;
      });

      mockDAO.upsertStoryRecord.mockImplementation(async () => {
        callOrder.push('upsertStoryRecord');
        return finalizedStoryRecord;
      });

      await FinalizeSessionRequestHandler.handle(sessionId);

      expect(callOrder).toEqual([
        'findSessionById',
        'updateSessionState',
        'upsertStoryRecord',
      ]);
    });

    it('should pass all collected responses to StoryRecord persistence', async () => {
      await FinalizeSessionRequestHandler.handle(sessionId);

      const [, responses] = mockDAO.upsertStoryRecord.mock.calls[0];
      expect(responses).toHaveLength(2);
      expect(responses[0]).toContain('payment processing');
      expect(responses[1]).toContain('migrating live traffic');
    });
  });

  // =========================================================================
  // TypeInvariant: types preserved across boundaries
  // =========================================================================

  describe('TypeInvariant: Response conforms to FinalizeSessionResponseSchema', () => {
    it('should produce a response conforming to the API contract', async () => {
      const result = await FinalizeSessionRequestHandler.handle(sessionId);

      const parsed = FinalizeSessionResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return exact literal values for sessionState and storyRecordStatus', async () => {
      const result = await FinalizeSessionRequestHandler.handle(sessionId);

      expect(result.sessionState).toBe('FINALIZE');
      expect(result.storyRecordStatus).toBe('FINALIZED');
    });
  });

  // =========================================================================
  // ErrorConsistency: each failure returns defined error, no partial updates
  // =========================================================================

  describe('ErrorConsistency: Error paths return standardized errors', () => {
    it('should throw SESSION_NOT_FOUND when session does not exist', async () => {
      mockDAO.findSessionById.mockResolvedValue(null);

      try {
        await FinalizeSessionRequestHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('SESSION_NOT_FOUND');
        expect((e as { statusCode: number }).statusCode).toBe(404);
      }

      // No state change or persistence should occur
      expect(mockDAO.updateSessionState).not.toHaveBeenCalled();
      expect(mockDAO.upsertStoryRecord).not.toHaveBeenCalled();
    });

    it('should throw INVALID_SESSION_STATE when session is not ACTIVE', async () => {
      mockDAO.findSessionById.mockResolvedValue({
        ...activeSession,
        state: 'DRAFT',
      });

      try {
        await FinalizeSessionRequestHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('INVALID_SESSION_STATE');
        expect((e as { statusCode: number }).statusCode).toBe(409);
      }

      expect(mockDAO.updateSessionState).not.toHaveBeenCalled();
      expect(mockDAO.upsertStoryRecord).not.toHaveBeenCalled();
    });

    it('should throw INCOMPLETE_SESSION when required inputs are not complete', async () => {
      mockDAO.findSessionById.mockResolvedValue({
        ...activeSession,
        requiredInputsComplete: false,
      });

      try {
        await FinalizeSessionRequestHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('INCOMPLETE_SESSION');
        expect((e as { statusCode: number }).statusCode).toBe(422);
      }

      expect(mockDAO.updateSessionState).not.toHaveBeenCalled();
      expect(mockDAO.upsertStoryRecord).not.toHaveBeenCalled();
    });

    it('should throw SESSION_PERSISTENCE_ERROR when state update fails', async () => {
      mockDAO.updateSessionState.mockRejectedValue(new Error('Connection refused'));

      try {
        await FinalizeSessionRequestHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('SESSION_PERSISTENCE_ERROR');
        expect((e as { statusCode: number }).statusCode).toBe(500);
        expect((e as { retryable: boolean }).retryable).toBe(true);
      }

      // StoryRecord should not be persisted when state update fails
      expect(mockDAO.upsertStoryRecord).not.toHaveBeenCalled();
    });

    it('should throw STORY_RECORD_PERSISTENCE_ERROR and rollback when StoryRecord fails', async () => {
      mockDAO.upsertStoryRecord.mockRejectedValue(new Error('Write failed'));

      // Rollback should succeed
      mockDAO.updateSessionState
        .mockResolvedValueOnce(finalizedSession)  // First call: update to FINALIZE
        .mockResolvedValueOnce({                   // Second call: rollback to ACTIVE
          ...finalizedSession,
          state: 'ACTIVE' as const,
        });

      try {
        await FinalizeSessionRequestHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('STORY_RECORD_PERSISTENCE_ERROR');
        expect((e as { statusCode: number }).statusCode).toBe(500);
      }

      // Verify rollback was attempted
      expect(mockDAO.updateSessionState).toHaveBeenCalledTimes(2);
      expect(mockDAO.updateSessionState).toHaveBeenLastCalledWith(sessionId, 'ACTIVE');
    });

    it('should throw VALIDATION_ERROR when sessionId is empty', async () => {
      try {
        await FinalizeSessionRequestHandler.handle('');
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('VALIDATION_ERROR');
        expect((e as { statusCode: number }).statusCode).toBe(400);
      }

      expect(mockDAO.findSessionById).not.toHaveBeenCalled();
    });
  });
});
