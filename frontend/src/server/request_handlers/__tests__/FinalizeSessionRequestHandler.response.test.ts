/**
 * FinalizeSessionRequestHandler.response.test.ts - Step 5: Return confirmation response
 *
 * TLA+ Properties:
 * - Reachability: Mock service success → call handler → { sessionState: "FINALIZE", storyRecordStatus: "FINALIZED" }
 * - TypeInvariant: Response matches FinalizeSessionResult shape
 * - ErrorConsistency: Service throws → appropriate error rethrown; unexpected error → INTERNAL_ERROR logged
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock dependencies
vi.mock('../../services/FinalizeSessionService', () => ({
  FinalizeSessionService: {
    finalize: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FinalizeSessionService } from '../../services/FinalizeSessionService';
import { FinalizeSessionRequestHandler } from '../FinalizeSessionRequestHandler';
import { FinalizeSessionError } from '../../error_definitions/FinalizeSessionErrors';
import { logger } from '../../logging/logger';

const mockService = vi.mocked(FinalizeSessionService);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const successResult = {
  sessionState: 'FINALIZE' as const,
  storyRecordStatus: 'FINALIZED' as const,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeSessionRequestHandler — Step 5: Return confirmation response', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call FinalizeSessionService.finalize with sessionId', async () => {
      mockService.finalize.mockResolvedValue(successResult);

      await FinalizeSessionRequestHandler.handle(sessionId);

      expect(mockService.finalize).toHaveBeenCalledWith(sessionId);
    });

    it('should return sessionState FINALIZE and storyRecordStatus FINALIZED', async () => {
      mockService.finalize.mockResolvedValue(successResult);

      const result = await FinalizeSessionRequestHandler.handle(sessionId);

      expect(result.sessionState).toBe('FINALIZE');
      expect(result.storyRecordStatus).toBe('FINALIZED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching FinalizeSessionResult shape', async () => {
      mockService.finalize.mockResolvedValue(successResult);

      const result = await FinalizeSessionRequestHandler.handle(sessionId);

      expect(result).toHaveProperty('sessionState');
      expect(result).toHaveProperty('storyRecordStatus');
      expect(typeof result.sessionState).toBe('string');
      expect(typeof result.storyRecordStatus).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow FinalizeSessionError from service', async () => {
      mockService.finalize.mockRejectedValue(
        new FinalizeSessionError('Session not found', 'SESSION_NOT_FOUND', 404),
      );

      try {
        await FinalizeSessionRequestHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect(e).toBeInstanceOf(FinalizeSessionError);
        expect((e as FinalizeSessionError).code).toBe('SESSION_NOT_FOUND');
        expect((e as FinalizeSessionError).statusCode).toBe(404);
      }
    });

    it('should throw VALIDATION_ERROR when sessionId is empty', async () => {
      try {
        await FinalizeSessionRequestHandler.handle('');
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('VALIDATION_ERROR');
        expect((e as { statusCode: number }).statusCode).toBe(400);
      }
    });

    it('should wrap unexpected errors in INTERNAL_ERROR and log', async () => {
      mockService.finalize.mockRejectedValue(new Error('Unexpected DB failure'));

      try {
        await FinalizeSessionRequestHandler.handle(sessionId);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('INTERNAL_ERROR');
        expect((e as { statusCode: number }).statusCode).toBe(500);
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Unexpected error'),
        expect.any(Error),
        expect.objectContaining({
          path: '308-finalize-voice-session-and-persist-storyrecord',
          resource: 'api-n8k2',
        }),
      );
    });
  });
});
