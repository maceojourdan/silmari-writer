/**
 * ModifySessionRequestHandler.test.ts - Step 2: Route request to handler
 *
 * TLA+ Properties:
 * - Reachability: valid command → service invoked with typed command.
 * - TypeInvariant: handler receives ModifySessionCommand { sessionId: string; action: 'ADD_VOICE' | 'FINALIZE' }
 * - ErrorConsistency: SessionError rethrown as-is; unknown errors wrapped in GenericError.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 309-reject-modifications-to-finalized-session
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../services/SessionModificationService', () => ({
  SessionModificationService: {
    processModification: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ModifySessionRequestHandler } from '../ModifySessionRequestHandler';
import { SessionModificationService } from '../../services/SessionModificationService';

const mockService = vi.mocked(SessionModificationService);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const rejectionResult = {
  success: false as const,
  error: new SessionError(
    'Session is already finalized and cannot be modified',
    'SESSION_ALREADY_FINALIZED',
    409,
    false,
  ),
};

const successResult = {
  success: true as const,
  record: {
    id: sessionId,
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'voice-001',
    userId: 'user-001',
    status: 'DRAFT' as const,
    content: 'A story in progress.',
  },
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ModifySessionRequestHandler — Step 2: Route request to handler', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should invoke service with sessionId and action from typed command', async () => {
      mockService.processModification.mockResolvedValue(rejectionResult);

      await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');

      expect(mockService.processModification).toHaveBeenCalledWith(sessionId, 'ADD_VOICE');
    });

    it('should return service result directly', async () => {
      mockService.processModification.mockResolvedValue(rejectionResult);

      const result = await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');

      expect(result).toEqual(rejectionResult);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should accept ADD_VOICE as a valid action', async () => {
      mockService.processModification.mockResolvedValue(rejectionResult);

      const result = await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');

      expect(result).toBeDefined();
    });

    it('should accept FINALIZE as a valid action', async () => {
      mockService.processModification.mockResolvedValue(rejectionResult);

      const result = await ModifySessionRequestHandler.handle(sessionId, 'FINALIZE');

      expect(mockService.processModification).toHaveBeenCalledWith(sessionId, 'FINALIZE');
      expect(result).toBeDefined();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow SessionError as-is', async () => {
      const error = new SessionError('Not found', 'SESSION_NOT_FOUND', 404, false);
      mockService.processModification.mockRejectedValue(error);

      try {
        await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('SESSION_NOT_FOUND');
        expect((e as SessionError).statusCode).toBe(404);
      }
    });

    it('should wrap unknown errors in GenericError', async () => {
      mockService.processModification.mockRejectedValue(new Error('Something unexpected'));

      try {
        await ModifySessionRequestHandler.handle(sessionId, 'ADD_VOICE');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }
    });
  });
});
