/**
 * Tests for ProcessVoiceResponseHandler
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 307-process-voice-input-and-progress-session
 *
 * TLA+ properties tested:
 * - Reachability: valid INIT session + valid payload → expect service called with validated command
 * - TypeInvariant: handler input conforms to Zod schema; output is service result type
 * - ErrorConsistency:
 *   - Session not INIT → expect SessionErrors.INVALID_STATE
 *   - Invalid payload → expect SessionErrors.INVALID_PAYLOAD
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionWithStoryRecordSchema } from '../../data_structures/AnswerSession';
import type { AnswerSession, SessionWithStoryRecord } from '../../data_structures/AnswerSession';

// Mock the SessionDAO
vi.mock('../../data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findAnswerSessionById: vi.fn(),
  },
}));

// Mock the SessionProgressionService
vi.mock('../../services/SessionProgressionService', () => ({
  SessionProgressionService: {
    progressSession: vi.fn(),
  },
}));

// Mock the logger
vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SessionDAO } from '../../data_access_objects/SessionDAO';
import { SessionProgressionService } from '../../services/SessionProgressionService';
import { logger } from '../../logging/logger';
import { ProcessVoiceResponseHandler } from '../ProcessVoiceResponseHandler';
import { SessionError } from '../../error_definitions/SessionErrors';

const mockDAO = vi.mocked(SessionDAO);
const mockService = vi.mocked(SessionProgressionService);
const mockLogger = vi.mocked(logger);

describe('ProcessVoiceResponseHandler', () => {
  const validPayload = {
    sessionId: '550e8400-e29b-41d4-a716-446655440000',
    transcript: 'I led a cross-functional team that reduced deployment time by 40 percent.',
  };

  const initSession: AnswerSession = {
    id: '550e8400-e29b-41d4-a716-446655440000',
    userId: 'user-123',
    state: 'INIT',
    createdAt: '2026-02-28T00:00:00Z',
    updatedAt: '2026-02-28T00:00:00Z',
  };

  const serviceResult: SessionWithStoryRecord = {
    session: {
      ...initSession,
      state: 'IN_PROGRESS',
      updatedAt: '2026-02-28T00:00:01Z',
    },
    storyRecord: {
      id: '660e8400-e29b-41d4-a716-446655440001',
      sessionId: initSession.id,
      status: 'IN_PROGRESS',
      content: validPayload.transcript,
      createdAt: '2026-02-28T00:00:00Z',
      updatedAt: '2026-02-28T00:00:01Z',
    },
  };

  function setupSuccessfulMocks() {
    mockDAO.findAnswerSessionById.mockResolvedValue(initSession);
    mockService.progressSession.mockResolvedValue(serviceResult);
  }

  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability: valid INIT session + valid payload → service called', () => {
    it('should fetch session, validate state, and call service', async () => {
      setupSuccessfulMocks();

      const result = await ProcessVoiceResponseHandler.handle(validPayload);

      expect(mockDAO.findAnswerSessionById).toHaveBeenCalledWith(validPayload.sessionId);
      expect(mockService.progressSession).toHaveBeenCalledWith(
        initSession,
        validPayload.transcript,
      );
      expect(result.session.state).toBe('IN_PROGRESS');
      expect(result.storyRecord.content).toBe(validPayload.transcript);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant: output matches SessionWithStoryRecord type', () => {
    it('should return result matching SessionWithStoryRecordSchema', async () => {
      setupSuccessfulMocks();

      const result = await ProcessVoiceResponseHandler.handle(validPayload);

      const parsed = SessionWithStoryRecordSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw INVALID_STATE when session is not in INIT state', async () => {
      const nonInitSession: AnswerSession = { ...initSession, state: 'IN_PROGRESS' };
      mockDAO.findAnswerSessionById.mockResolvedValue(nonInitSession);

      try {
        await ProcessVoiceResponseHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('INVALID_STATE');
      }
    });

    it('should throw INVALID_PAYLOAD when sessionId is missing', async () => {
      try {
        await ProcessVoiceResponseHandler.handle({
          sessionId: '',
          transcript: 'Some transcript',
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('INVALID_PAYLOAD');
      }
    });

    it('should throw INVALID_PAYLOAD when transcript is empty', async () => {
      try {
        await ProcessVoiceResponseHandler.handle({
          sessionId: '550e8400-e29b-41d4-a716-446655440000',
          transcript: '',
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('INVALID_PAYLOAD');
      }
    });

    it('should throw INVALID_STATE when session is not found', async () => {
      mockDAO.findAnswerSessionById.mockResolvedValue(null);

      try {
        await ProcessVoiceResponseHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('INVALID_STATE');
      }
    });

    it('should rethrow SessionError from service as-is', async () => {
      mockDAO.findAnswerSessionById.mockResolvedValue(initSession);
      const { SessionErrors } = await import('../../error_definitions/SessionErrors');
      mockService.progressSession.mockRejectedValue(
        SessionErrors.InvalidTransition('Cannot transition from INIT'),
      );

      try {
        await ProcessVoiceResponseHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('INVALID_TRANSITION');
      }
    });

    it('should wrap unexpected errors and log them', async () => {
      mockDAO.findAnswerSessionById.mockResolvedValue(initSession);
      mockService.progressSession.mockRejectedValue(new TypeError('unexpected'));

      try {
        await ProcessVoiceResponseHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(mockLogger.error).toHaveBeenCalled();
      }
    });
  });
});
