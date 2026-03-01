/**
 * Tests for InitializeSessionService
 *
 * Resource: db-h2s4 (service)
 * Path: 310-initialize-new-session-with-provided-objects
 *
 * TLA+ properties tested:
 * - Reachability: createSession(validObjects) → returned session has embedded objects, state "initialized"
 * - TypeInvariant: returned object conforms to InitializedSession type
 * - ErrorConsistency: internal inconsistency → SessionErrors.ServiceError
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '../../error_definitions/SessionErrors';
import { InitializedSessionSchema } from '../../data_structures/InitializedSession';
import type { ResumeObject, JobObject, QuestionObject } from '../../data_structures/SessionObjects';

// Mock the DAO
vi.mock('../../data_access_objects/InitializeSessionDAO', () => ({
  InitializeSessionDAO: {
    getActiveSession: vi.fn().mockResolvedValue(null),
    persist: vi.fn(),
  },
}));

import { InitializeSessionDAO } from '../../data_access_objects/InitializeSessionDAO';
import { InitializeSessionService } from '../InitializeSessionService';

const mockDAO = vi.mocked(InitializeSessionDAO);

describe('InitializeSessionService — Step 3: Create session entity', () => {
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

  const mockPersistedSession = {
    id: '550e8400-e29b-41d4-a716-446655440000',
    resume: validResume,
    job: validJob,
    question: validQuestion,
    state: 'initialized' as const,
    createdAt: new Date().toISOString(),
  };

  beforeEach(() => {
    vi.clearAllMocks();
    // Ensure no active session exists (Path 310 normal flow)
    mockDAO.getActiveSession.mockResolvedValue(null);
  });

  describe('Reachability: createSession(validObjects) → session with embedded objects and state "initialized"', () => {
    it('should create session entity with embedded objects and state "initialized"', async () => {
      mockDAO.persist.mockResolvedValue(mockPersistedSession);

      const result = await InitializeSessionService.createSession({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      expect(result).toBeDefined();
      expect(result.resume).toEqual(validResume);
      expect(result.job).toEqual(validJob);
      expect(result.question).toEqual(validQuestion);
      expect(result.state).toBe('initialized');
    });

    it('should call DAO.persist with session entity that has state "initialized"', async () => {
      mockDAO.persist.mockResolvedValue(mockPersistedSession);

      await InitializeSessionService.createSession({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      expect(mockDAO.persist).toHaveBeenCalledTimes(1);
      const persistArg = mockDAO.persist.mock.calls[0][0];
      expect(persistArg.state).toBe('initialized');
      expect(persistArg.resume).toEqual(validResume);
      expect(persistArg.job).toEqual(validJob);
      expect(persistArg.question).toEqual(validQuestion);
      expect(persistArg.createdAt).toBeDefined();
    });
  });

  describe('TypeInvariant: returned object conforms to InitializedSession type', () => {
    it('should return object matching InitializedSession schema', async () => {
      mockDAO.persist.mockResolvedValue(mockPersistedSession);

      const result = await InitializeSessionService.createSession({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const parsed = InitializedSessionSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: inconsistency → SessionErrors.ServiceError', () => {
    it('should throw SERVICE_ERROR when DAO throws a non-session error', async () => {
      mockDAO.persist.mockRejectedValue(new Error('Unexpected DAO failure'));

      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: validJob,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('SERVICE_ERROR');
      }
    });

    it('should rethrow PERSISTENCE_FAILURE from DAO as-is', async () => {
      const { SessionErrors } = await import('../../error_definitions/SessionErrors');
      mockDAO.persist.mockRejectedValue(
        SessionErrors.PersistenceFailure('DB connection lost'),
      );

      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: validJob,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('PERSISTENCE_FAILURE');
      }
    });
  });
});
