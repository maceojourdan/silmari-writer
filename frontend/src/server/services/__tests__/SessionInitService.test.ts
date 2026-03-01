/**
 * Tests for SessionInitService
 *
 * Resource: db-h2s4 (service)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: valid objects → returns { sessionId, resumeId, jobId, questionId }
 * - TypeInvariant: IDs are UUID strings
 * - ErrorConsistency: DAO throws → expect SessionErrors.PersistenceFailure
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '../../error_definitions/SessionErrors';
import type { ParsedSessionInput, SessionInitResult } from '../../data_structures/SessionObjects';

// Mock the DAO
vi.mock('../../data_access_objects/SessionInitDAO', () => ({
  SessionInitDAO: {
    insertResume: vi.fn(),
    insertJob: vi.fn(),
    insertQuestion: vi.fn(),
    insertSession: vi.fn(),
  },
}));

import { SessionInitDAO } from '../../data_access_objects/SessionInitDAO';
import { SessionInitService } from '../SessionInitService';

const mockDAO = vi.mocked(SessionInitDAO);

describe('SessionInitService', () => {
  const validInput: ParsedSessionInput = {
    resume: {
      content: 'Experienced software engineer...',
      name: 'Uploaded Resume',
      wordCount: 3,
    },
    job: {
      title: 'Senior Developer',
      description: 'Job description...',
      sourceType: 'text',
      sourceValue: 'Job description...',
    },
    question: {
      text: 'Tell me about a challenge.',
    },
  };

  const mockResumeId = '550e8400-e29b-41d4-a716-446655440001';
  const mockJobId = '550e8400-e29b-41d4-a716-446655440002';
  const mockQuestionId = '550e8400-e29b-41d4-a716-446655440003';
  const mockSessionId = '550e8400-e29b-41d4-a716-446655440000';

  function setupSuccessfulMocks() {
    mockDAO.insertResume.mockResolvedValue(mockResumeId);
    mockDAO.insertJob.mockResolvedValue(mockJobId);
    mockDAO.insertQuestion.mockResolvedValue(mockQuestionId);
    mockDAO.insertSession.mockResolvedValue(mockSessionId);
  }

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: valid objects → returns IDs', () => {
    it('should insert all objects and return generated IDs', async () => {
      setupSuccessfulMocks();

      const result = await SessionInitService.initialize(validInput);

      expect(mockDAO.insertResume).toHaveBeenCalledWith(validInput.resume);
      expect(mockDAO.insertJob).toHaveBeenCalledWith(validInput.job);
      expect(mockDAO.insertQuestion).toHaveBeenCalledWith(validInput.question);
      expect(mockDAO.insertSession).toHaveBeenCalledTimes(1);
      expect(result.sessionId).toBe(mockSessionId);
      expect(result.resumeId).toBe(mockResumeId);
      expect(result.jobId).toBe(mockJobId);
      expect(result.questionId).toBe(mockQuestionId);
    });

    it('should pass resume, job, and question IDs to session insert', async () => {
      setupSuccessfulMocks();

      await SessionInitService.initialize(validInput);

      const sessionArg = mockDAO.insertSession.mock.calls[0][0];
      expect(sessionArg.resumeId).toBe(mockResumeId);
      expect(sessionArg.jobId).toBe(mockJobId);
      expect(sessionArg.questionId).toBe(mockQuestionId);
      expect(sessionArg.status).toBe('INITIALIZED');
    });
  });

  describe('TypeInvariant: IDs are UUID strings', () => {
    it('should return IDs matching UUID format', async () => {
      setupSuccessfulMocks();

      const result = await SessionInitService.initialize(validInput);

      const uuidRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
      expect(result.sessionId).toMatch(uuidRegex);
      expect(result.resumeId).toMatch(uuidRegex);
      expect(result.jobId).toMatch(uuidRegex);
      expect(result.questionId).toMatch(uuidRegex);
    });
  });

  describe('ErrorConsistency: DAO failures → PERSISTENCE_FAILURE', () => {
    it('should throw PERSISTENCE_FAILURE when insertResume fails', async () => {
      setupSuccessfulMocks();
      mockDAO.insertResume.mockRejectedValue(new Error('DB connection lost'));

      await expect(SessionInitService.initialize(validInput)).rejects.toThrow(
        SessionError,
      );

      try {
        await SessionInitService.initialize(validInput);
      } catch (e) {
        expect((e as SessionError).code).toBe('PERSISTENCE_FAILURE');
        expect((e as SessionError).retryable).toBe(true);
      }
    });

    it('should throw PERSISTENCE_FAILURE when insertJob fails', async () => {
      setupSuccessfulMocks();
      mockDAO.insertJob.mockRejectedValue(new Error('Constraint violation'));

      await expect(SessionInitService.initialize(validInput)).rejects.toThrow(
        SessionError,
      );

      try {
        await SessionInitService.initialize(validInput);
      } catch (e) {
        expect((e as SessionError).code).toBe('PERSISTENCE_FAILURE');
      }
    });

    it('should throw PERSISTENCE_FAILURE when insertQuestion fails', async () => {
      setupSuccessfulMocks();
      mockDAO.insertQuestion.mockRejectedValue(new Error('Timeout'));

      await expect(SessionInitService.initialize(validInput)).rejects.toThrow(
        SessionError,
      );
    });

    it('should throw PERSISTENCE_FAILURE when insertSession fails', async () => {
      setupSuccessfulMocks();
      mockDAO.insertSession.mockRejectedValue(new Error('FK constraint'));

      await expect(SessionInitService.initialize(validInput)).rejects.toThrow(
        SessionError,
      );

      try {
        await SessionInitService.initialize(validInput);
      } catch (e) {
        expect((e as SessionError).code).toBe('PERSISTENCE_FAILURE');
      }
    });
  });
});
