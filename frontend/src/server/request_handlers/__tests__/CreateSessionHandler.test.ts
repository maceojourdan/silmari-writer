/**
 * CreateSessionHandler Tests - Step 3: Request handler invokes session initialization logic
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * TLA+ properties tested:
 * - Reachability: Valid command → service.initializeSession(userId) called
 * - TypeInvariant: Service return type matches SessionInitializationResult
 * - ErrorConsistency: Malformed command → VALIDATION_ERROR from HttpErrors
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock dependencies
vi.mock('@/server/services/SessionInitializationService', () => ({
  SessionInitializationService: {
    initializeSession: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { CreateSessionHandler } from '../CreateSessionHandler';
import { SessionInitializationService } from '@/server/services/SessionInitializationService';
import { HttpError } from '@/server/error_definitions/HttpErrors';
import { SessionError } from '@/server/error_definitions/SessionErrors';

const mockService = vi.mocked(SessionInitializationService);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('CreateSessionHandler — Step 3: Request handler invokes session initialization logic', () => {
  const validCommand = { userId: 'user-abc12345' };

  const mockResult = {
    sessionId: '550e8400-e29b-41d4-a716-446655440000',
    storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
    state: 'INIT' as const,
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call service.initializeSession with userId', async () => {
      mockService.initializeSession.mockResolvedValue(mockResult);

      await CreateSessionHandler.handle(validCommand);

      expect(mockService.initializeSession).toHaveBeenCalledWith('user-abc12345');
    });

    it('should return the service result', async () => {
      mockService.initializeSession.mockResolvedValue(mockResult);

      const result = await CreateSessionHandler.handle(validCommand);

      expect(result).toEqual(mockResult);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching SessionInitializationResult shape', async () => {
      mockService.initializeSession.mockResolvedValue(mockResult);

      const result = await CreateSessionHandler.handle(validCommand);

      expect(result).toHaveProperty('sessionId');
      expect(result).toHaveProperty('storyRecordId');
      expect(result).toHaveProperty('state');
      expect(result.state).toBe('INIT');
      expect(typeof result.sessionId).toBe('string');
      expect(typeof result.storyRecordId).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw VALIDATION_ERROR when userId is empty', async () => {
      await expect(
        CreateSessionHandler.handle({ userId: '' }),
      ).rejects.toThrow(HttpError);

      await expect(
        CreateSessionHandler.handle({ userId: '' }),
      ).rejects.toMatchObject({
        code: 'VALIDATION_ERROR',
      });
    });

    it('should throw VALIDATION_ERROR when userId is whitespace-only', async () => {
      await expect(
        CreateSessionHandler.handle({ userId: '   ' }),
      ).rejects.toMatchObject({
        code: 'VALIDATION_ERROR',
      });
    });

    it('should rethrow SessionError as-is', async () => {
      const sessionError = new SessionError('Persistence failed', 'SESSION_PERSISTENCE_ERROR', 500, true);
      mockService.initializeSession.mockRejectedValue(sessionError);

      await expect(
        CreateSessionHandler.handle(validCommand),
      ).rejects.toBe(sessionError);
    });

    it('should wrap unexpected errors in INTERNAL_ERROR', async () => {
      mockService.initializeSession.mockRejectedValue(new Error('Unexpected crash'));

      await expect(
        CreateSessionHandler.handle(validCommand),
      ).rejects.toMatchObject({
        code: 'INTERNAL_ERROR',
        statusCode: 500,
      });
    });
  });
});
