/**
 * SessionModificationService.reject.test.ts - Step 5: Reject modification and preserve state
 *
 * TLA+ Properties:
 * - Reachability: when verifier returns disallowed, service returns SessionErrors.SessionAlreadyFinalized.
 * - TypeInvariant: assert response shape { status: 409; code: 'SESSION_ALREADY_FINALIZED' }
 * - ErrorConsistency:
 *   - Spy on StoryRecordDAO.update → assert NOT called.
 *   - If error mapping throws, expect fallback CONFLICT_GENERIC.
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

// Mock the StoryRecordStateVerifier (for error mapping fallback test)
vi.mock('@/server/verifiers/StoryRecordStateVerifier', async (importOriginal) => {
  const original = await importOriginal<typeof import('@/server/verifiers/StoryRecordStateVerifier')>();
  return {
    ...original,
    StoryRecordStateVerifier: {
      ...original.StoryRecordStateVerifier,
      canModify: original.StoryRecordStateVerifier.canModify,
    },
  };
});

import { SessionModificationService } from '../SessionModificationService';
import { StoryRecordDAO } from '@/server/data_access_objects/StoryRecordDAO';
import { StoryRecordStateVerifier } from '@/server/verifiers/StoryRecordStateVerifier';
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

const draftRecord: StoryRecord = {
  ...finalizedRecord,
  status: 'DRAFT',
};

// ---------------------------------------------------------------------------
// Tests — Step 5: Reject modification and preserve state
// ---------------------------------------------------------------------------

describe('SessionModificationService — Step 5: Reject modification and preserve state', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return error result with SESSION_ALREADY_FINALIZED when verifier disallows', async () => {
      mockDAO.findById.mockResolvedValue(finalizedRecord);

      const result = await SessionModificationService.processModification(
        sessionId,
        'ADD_VOICE',
      );

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.code).toBe('SESSION_ALREADY_FINALIZED');
      }
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return error response with status 409 and code SESSION_ALREADY_FINALIZED', async () => {
      mockDAO.findById.mockResolvedValue(finalizedRecord);

      const result = await SessionModificationService.processModification(
        sessionId,
        'ADD_VOICE',
      );

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.statusCode).toBe(409);
        expect(result.error.code).toBe('SESSION_ALREADY_FINALIZED');
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should NOT call StoryRecordDAO.updateDraft when modification is rejected', async () => {
      mockDAO.findById.mockResolvedValue(finalizedRecord);

      await SessionModificationService.processModification(sessionId, 'ADD_VOICE');

      expect(mockDAO.updateDraft).not.toHaveBeenCalled();
    });

    it('should fallback to CONFLICT_GENERIC if error mapping fails', async () => {
      mockDAO.findById.mockResolvedValue(finalizedRecord);

      // Override canModify to throw an unexpected error during verification
      const originalCanModify = StoryRecordStateVerifier.canModify;
      vi.spyOn(StoryRecordStateVerifier, 'canModify').mockImplementation(() => {
        throw new Error('Unexpected verifier failure');
      });

      const result = await SessionModificationService.processModification(
        sessionId,
        'ADD_VOICE',
      );

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.code).toBe('CONFLICT_GENERIC');
      }

      // Restore
      vi.mocked(StoryRecordStateVerifier.canModify).mockRestore();
    });

    it('should return success result when StoryRecord is in DRAFT state', async () => {
      mockDAO.findById.mockResolvedValue(draftRecord);

      const result = await SessionModificationService.processModification(
        sessionId,
        'ADD_VOICE',
      );

      expect(result.success).toBe(true);
    });
  });
});
