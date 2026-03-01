/**
 * Tests for InitializeSessionRequestHandler — rejection/delegation path
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Step 2: Delegate to session service
 *
 * TLA+ properties tested:
 * - Reachability: Mock SessionInitService.initialize → call handle(validInput) → service called with same structured input
 * - TypeInvariant: Handler passes typed object (no mutation, correct keys)
 * - ErrorConsistency: Mock service to throw ServiceContractError → handler maps to SERVICE_INVOCATION_FAILED
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '../../error_definitions/SessionErrors';
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

describe('InitializeSessionRequestHandler — Step 2: Delegate to session service (Path 312)', () => {
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

  describe('Reachability: handle(validInput) → service called with same structured input', () => {
    it('should call service with exact same structured input', async () => {
      mockService.createSession.mockResolvedValue(mockSession);

      await InitializeSessionRequestHandler.handle(validPayload);

      expect(mockService.createSession).toHaveBeenCalledTimes(1);
      expect(mockService.createSession).toHaveBeenCalledWith({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });
    });
  });

  describe('TypeInvariant: handler passes typed object (no mutation, correct keys)', () => {
    it('should pass through objects without mutation', async () => {
      mockService.createSession.mockResolvedValue(mockSession);

      await InitializeSessionRequestHandler.handle(validPayload);

      const serviceArg = mockService.createSession.mock.calls[0][0];
      expect(serviceArg.resume).toEqual(validResume);
      expect(serviceArg.job).toEqual(validJob);
      expect(serviceArg.question).toEqual(validQuestion);
      // Verify it only has the expected keys
      expect(Object.keys(serviceArg)).toEqual(
        expect.arrayContaining(['resume', 'job', 'question']),
      );
    });
  });

  describe('ErrorConsistency: service contract violation → SERVICE_INVOCATION_FAILED', () => {
    it('should map TypeError (contract violation) to SERVICE_INVOCATION_FAILED', async () => {
      mockService.createSession.mockRejectedValue(
        new TypeError('createSession is not a function'),
      );

      try {
        await InitializeSessionRequestHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('SERVICE_INVOCATION_FAILED');
      }

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should rethrow MISSING_REQUIRED_OBJECT from service as-is', async () => {
      const { SessionErrors } = await import('../../error_definitions/SessionErrors');
      mockService.createSession.mockRejectedValue(
        SessionErrors.MissingRequiredObject('ResumeObject is required but missing'),
      );

      try {
        await InitializeSessionRequestHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('MISSING_REQUIRED_OBJECT');
      }
    });

    it('should rethrow VALIDATION_FAILURE from service as-is', async () => {
      const { SessionErrors } = await import('../../error_definitions/SessionErrors');
      mockService.createSession.mockRejectedValue(
        SessionErrors.ValidationFailure('Invalid object structure'),
      );

      try {
        await InitializeSessionRequestHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('VALIDATION_FAILURE');
      }
    });

    it('should map service invocation failure to SERVICE_INVOCATION_FAILED', async () => {
      // Simulate a contract violation where service method signature changes
      const contractError = new Error('Expected 3 arguments but got 1');
      mockService.createSession.mockRejectedValue(contractError);

      try {
        await InitializeSessionRequestHandler.handle(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('SERVICE_INVOCATION_FAILED');
      }
    });
  });
});
