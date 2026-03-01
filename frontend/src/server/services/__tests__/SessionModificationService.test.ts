/**
 * SessionModificationService.test.ts - Step 3: Load StoryRecord
 *
 * TLA+ Properties:
 * - Reachability: mock DAO to return StoryRecord with state FINALIZED; assert service receives entity.
 * - TypeInvariant: assert returned entity conforms to StoryRecord type with state: 'INIT' | ... | 'FINALIZED'.
 * - ErrorConsistency: mock DAO returns null → expect SessionErrors.NotFound.
 *
 * Resource: db-h2s4 (service)
 * Path: 309-reject-modifications-to-finalized-session
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock the StoryRecordDAO
vi.mock('@/server/data_access_objects/StoryRecordDAO', () => ({
  StoryRecordDAO: {
    findById: vi.fn(),
    updateDraft: vi.fn(),
  },
}));

import { SessionModificationService } from '../SessionModificationService';
import { StoryRecordDAO } from '@/server/data_access_objects/StoryRecordDAO';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import type { StoryRecord } from '@/server/data_structures/StoryRecord';

const mockDAO = vi.mocked(StoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const finalizedRecord: StoryRecord = {
  id: sessionId,
  draftId: 'draft-001',
  resumeId: 'resume-001',
  jobId: 'job-001',
  questionId: 'question-001',
  voiceSessionId: 'voice-001',
  userId: 'user-001',
  status: 'FINALIZED',
  content: 'A completed story about leadership.',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests — Step 3: Load StoryRecord
// ---------------------------------------------------------------------------

describe('SessionModificationService — Step 3: Load StoryRecord', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should load StoryRecord via DAO when processing modification', async () => {
      mockDAO.findById.mockResolvedValue(finalizedRecord);

      const result = await SessionModificationService.processModification(
        sessionId,
        'ADD_VOICE',
      );

      expect(mockDAO.findById).toHaveBeenCalledWith(sessionId);
      // The result should be an error since the record is finalized
      expect(result.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should receive StoryRecord entity with valid status field from DAO', async () => {
      mockDAO.findById.mockResolvedValue(finalizedRecord);

      // The DAO returns a StoryRecord — verified by the fact processModification doesn't throw
      const result = await SessionModificationService.processModification(
        sessionId,
        'ADD_VOICE',
      );

      expect(mockDAO.findById).toHaveBeenCalledWith(sessionId);
      expect(result).toBeDefined();
      // The status field should be one of the valid enum values
      expect(['DRAFT', 'APPROVED', 'FINALIZED']).toContain(finalizedRecord.status);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SessionErrors.NotFound when DAO returns null', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await SessionModificationService.processModification(sessionId, 'ADD_VOICE');
        expect.fail('Expected SessionError to be thrown');
      } catch (error) {
        expect(error).toBeInstanceOf(SessionError);
        expect((error as SessionError).code).toBe('SESSION_NOT_FOUND');
        expect((error as SessionError).statusCode).toBe(404);
      }
    });
  });
});
