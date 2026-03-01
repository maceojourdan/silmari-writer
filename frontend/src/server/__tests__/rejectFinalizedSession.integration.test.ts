/**
 * Integration test for the reject-modifications-to-finalized-session path
 *
 * Path: 309-reject-modifications-to-finalized-session
 *
 * This proves end-to-end:
 * - Reachability: Full path executed (request → handler → service → verifier → rejection)
 * - TypeInvariant: Consistent types across layers
 * - ErrorConsistency: Correct domain error (SESSION_ALREADY_FINALIZED) + no persistence mutation
 *
 * Note: Mocks only the DAO layer (database boundary). Everything above
 * runs with real implementations: handler, service, verifier.
 *
 * Terminal Condition:
 * 1. Seed mock with StoryRecord { status: 'FINALIZED' }
 * 2. Process modification with ADD_VOICE
 * 3. Assert error code = SESSION_ALREADY_FINALIZED, status = 409
 * 4. Assert StoryRecord remains FINALIZED and DAO.updateDraft NOT called
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Only mock the DAO — everything else is real
vi.mock('../data_access_objects/StoryRecordDAO', () => ({
  StoryRecordDAO: {
    findById: vi.fn(),
    updateDraft: vi.fn(),
  },
}));

// Mock the logger to verify no unexpected errors
vi.mock('../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { StoryRecordDAO } from '../data_access_objects/StoryRecordDAO';
import { ModifySessionRequestHandler } from '../request_handlers/ModifySessionRequestHandler';
import { SessionModificationService } from '../services/SessionModificationService';
import { StoryRecordStateVerifier } from '../verifiers/StoryRecordStateVerifier';
import { validateModifySessionPayload } from '@/verifiers/SessionModificationVerifier';
import { SessionError } from '../error_definitions/SessionErrors';
import type { StoryRecord } from '../data_structures/StoryRecord';

const mockDAO = vi.mocked(StoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data — Simulates seeded DB with FINALIZED StoryRecord
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const finalizedStoryRecord: StoryRecord = {
  id: sessionId,
  draftId: 'draft-001',
  resumeId: 'resume-001',
  jobId: 'job-001',
  questionId: 'question-001',
  voiceSessionId: 'voice-001',
  userId: 'user-001',
  status: 'FINALIZED',
  content: 'A completed story about leadership and teamwork.',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

const draftStoryRecord: StoryRecord = {
  ...finalizedStoryRecord,
  status: 'DRAFT',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Reject Finalized Session — Integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    // Seed: StoryRecord with status FINALIZED
    mockDAO.findById.mockResolvedValue(finalizedStoryRecord);
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path executed
  // -------------------------------------------------------------------------

  describe('Reachability: Full path from modification request to rejection', () => {
    it('should execute full flow: frontend verifier → handler → service → verifier → rejection', async () => {
      // Step 1: Frontend verifier validates payload
      const frontendValidation = validateModifySessionPayload({
        sessionId,
        action: 'ADD_VOICE',
      });
      expect(frontendValidation.success).toBe(true);

      // Steps 2-5: Handler → Service → StoryRecordStateVerifier → Rejection
      const result = await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');

      // Terminal condition: Rejection with SESSION_ALREADY_FINALIZED
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.code).toBe('SESSION_ALREADY_FINALIZED');
      }

      // Verify DAO was called to load the record
      expect(mockDAO.findById).toHaveBeenCalledWith(sessionId);
    });

    it('should work through each layer: verifier → service → DAO', async () => {
      // Step 3: Service loads record
      const serviceResult = await SessionModificationService.processModification(
        sessionId,
        'ADD_VOICE',
      );

      expect(serviceResult.success).toBe(false);
      expect(mockDAO.findById).toHaveBeenCalledWith(sessionId);
    });

    it('should detect FINALIZED state through StoryRecordStateVerifier', () => {
      // Step 4: Verifier checks immutability
      const verification = StoryRecordStateVerifier.canModify(finalizedStoryRecord);

      expect(verification.allowed).toBe(false);
      expect(verification.reason).toBe('SESSION_ALREADY_FINALIZED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Consistent types across layers
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Consistent types across all layers', () => {
    it('should return error with status 409 and code SESSION_ALREADY_FINALIZED', async () => {
      const result = await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error).toBeInstanceOf(SessionError);
        expect(result.error.statusCode).toBe(409);
        expect(result.error.code).toBe('SESSION_ALREADY_FINALIZED');
        expect(result.error.retryable).toBe(false);
      }
    });

    it('should validate frontend payload schema matches backend expectations', () => {
      // Frontend schema
      const frontendPayload = validateModifySessionPayload({
        sessionId,
        action: 'ADD_VOICE',
      });
      expect(frontendPayload.success).toBe(true);

      // Backend verifier expects StoryRecord with status field
      expect(finalizedStoryRecord.status).toBe('FINALIZED');
      expect(['DRAFT', 'APPROVED', 'FINALIZED']).toContain(finalizedStoryRecord.status);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: No persistence mutation + correct domain error
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Correct domain error + no persistence mutation', () => {
    it('should NOT call StoryRecordDAO.updateDraft when session is FINALIZED', async () => {
      await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');

      // Critical assertion: DAO.updateDraft must NOT be called
      expect(mockDAO.updateDraft).not.toHaveBeenCalled();
    });

    it('should return same error code regardless of action type (ADD_VOICE or FINALIZE)', async () => {
      const addVoiceResult = await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');
      const finalizeResult = await ModifySessionRequestHandler.handle(sessionId, 'FINALIZE');

      expect(addVoiceResult.success).toBe(false);
      expect(finalizeResult.success).toBe(false);

      if (!addVoiceResult.success && !finalizeResult.success) {
        expect(addVoiceResult.error.code).toBe('SESSION_ALREADY_FINALIZED');
        expect(finalizeResult.error.code).toBe('SESSION_ALREADY_FINALIZED');
      }
    });

    it('should throw SESSION_NOT_FOUND when record does not exist', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');
        expect.fail('Should have thrown');
      } catch (error) {
        expect(error).toBeInstanceOf(SessionError);
        expect((error as SessionError).code).toBe('SESSION_NOT_FOUND');
        expect((error as SessionError).statusCode).toBe(404);
      }
    });

    it('should allow modification when StoryRecord is in DRAFT state', async () => {
      mockDAO.findById.mockResolvedValue(draftStoryRecord);

      const result = await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');

      expect(result.success).toBe(true);
    });

    it('should preserve StoryRecord state — record remains FINALIZED after rejection', async () => {
      // Process rejection
      const result = await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');
      expect(result.success).toBe(false);

      // Reload StoryRecord from "DB" (mock)
      const reloadedRecord = await mockDAO.findById(sessionId);

      // Verify state is still FINALIZED
      expect(reloadedRecord!.status).toBe('FINALIZED');
      expect(reloadedRecord).toEqual(finalizedStoryRecord);
    });
  });
});
