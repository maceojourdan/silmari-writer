/**
 * Tests for InitializeSessionRequestHandler
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 310-initialize-new-session-with-provided-objects
 *
 * TLA+ properties tested:
 * - Reachability: handle(validPayload) → service called with validated objects → returns InitializedSession
 * - TypeInvariant: returned value contains typed InitializedSession DTO
 * - ErrorConsistency: invalid QuestionObject (empty text) → SessionErrors.ValidationFailure, service NOT called
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '../../error_definitions/SessionErrors';
import { InitializedSessionSchema } from '../../data_structures/InitializedSession';
import type { ResumeObject, JobObject, QuestionObject } from '../../data_structures/SessionObjects';

// Mock the service
vi.mock('../../services/InitializeSessionService', () => ({
  InitializeSessionService: {
    createSession: vi.fn(),
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

import { InitializeSessionService } from '../../services/InitializeSessionService';
import { logger } from '../../logging/logger';
import { InitializeSessionRequestHandler } from '../InitializeSessionRequestHandler';

const mockService = vi.mocked(InitializeSessionService);
const mockLogger = vi.mocked(logger);

describe('InitializeSessionRequestHandler — Step 2: Validate provided objects', () => {
  const validResume: ResumeObject = {
    content: 'Experienced software engineer with 10 years of expertise in TypeScript.',
    name: 'John Doe Resume',
    wordCount: 10,
  };

  const validJob: JobObject = {
    title: 'Senior Software Engineer',
    description: 'We are looking for a senior engineer to lead our TypeScript team.',
    sourceType: 'text',
    sourceValue: 'We are looking for a senior engineer to lead our TypeScript team.',
  };

  const validQuestion: QuestionObject = {
    text: 'Tell me about a time you led a complex technical project.',
  };

  const validPayload = {
    resume: validResume,
    job: validJob,
    question: validQuestion,
  };

  const mockSession = {
    id: '550e8400-e29b-41d4-a716-446655440000',
    resume: validResume,
    job: validJob,
    question: validQuestion,
    state: 'initialized' as const,
    createdAt: new Date().toISOString(),
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: handle(validPayload) → validated objects passed to service', () => {
    it('should validate payload and call service with validated objects', async () => {
      mockService.createSession.mockResolvedValue(mockSession);

      const result = await InitializeSessionRequestHandler.handle(validPayload);

      expect(mockService.createSession).toHaveBeenCalledTimes(1);
      expect(mockService.createSession).toHaveBeenCalledWith({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });
      expect(result).toBeDefined();
      expect(result.id).toBe(mockSession.id);
    });

    it('should return the InitializedSession from service', async () => {
      mockService.createSession.mockResolvedValue(mockSession);

      const result = await InitializeSessionRequestHandler.handle(validPayload);

      expect(result.state).toBe('initialized');
      expect(result.resume).toEqual(validResume);
      expect(result.job).toEqual(validJob);
      expect(result.question).toEqual(validQuestion);
    });
  });

  describe('TypeInvariant: returned value contains typed InitializedSession DTO', () => {
    it('should return object matching InitializedSession schema', async () => {
      mockService.createSession.mockResolvedValue(mockSession);

      const result = await InitializeSessionRequestHandler.handle(validPayload);

      const parsed = InitializedSessionSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: invalid objects → ValidationFailure, service NOT called', () => {
    it('should throw VALIDATION_FAILURE for empty question text', async () => {
      const invalidPayload = {
        resume: validResume,
        job: validJob,
        question: { text: '' },
      };

      try {
        await InitializeSessionRequestHandler.handle(invalidPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('VALIDATION_FAILURE');
      }

      expect(mockService.createSession).not.toHaveBeenCalled();
    });

    it('should throw VALIDATION_FAILURE for missing resume content', async () => {
      const invalidPayload = {
        resume: { content: '', name: 'Empty', wordCount: 0 },
        job: validJob,
        question: validQuestion,
      };

      try {
        await InitializeSessionRequestHandler.handle(invalidPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('VALIDATION_FAILURE');
      }

      expect(mockService.createSession).not.toHaveBeenCalled();
    });

    it('should throw VALIDATION_FAILURE for missing job title', async () => {
      const invalidPayload = {
        resume: validResume,
        job: { ...validJob, title: '' },
        question: validQuestion,
      };

      try {
        await InitializeSessionRequestHandler.handle(invalidPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('VALIDATION_FAILURE');
      }

      expect(mockService.createSession).not.toHaveBeenCalled();
    });

    it('should rethrow SessionError from service as-is', async () => {
      const { SessionErrors } = await import('../../error_definitions/SessionErrors');
      mockService.createSession.mockRejectedValue(
        SessionErrors.PersistenceFailure('DB down'),
      );

      try {
        await InitializeSessionRequestHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('PERSISTENCE_FAILURE');
      }
    });

    it('should wrap unknown errors in SessionErrors.ServiceInvocationFailed and log', async () => {
      mockService.createSession.mockRejectedValue(new TypeError('undefined is not a function'));

      try {
        await InitializeSessionRequestHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('SERVICE_INVOCATION_FAILED');
      }

      expect(mockLogger.error).toHaveBeenCalled();
    });
  });
});
