/**
 * Tests for InitializeSessionService — validation of required domain objects
 *
 * Resource: db-h2s4 (service)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Step 3: Validate required domain objects
 *
 * TLA+ properties tested:
 * - Reachability: Call initialize() with one invalid object → validation logic executes
 * - TypeInvariant: Provide structurally valid objects → expect ValidationSuccess | ValidationFailure result type
 * - ErrorConsistency: Missing/invalid objects → MISSING_REQUIRED_OBJECT with specific object names; DAO.create NOT called
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '../../error_definitions/SessionErrors';
import type { ResumeObject, JobObject, QuestionObject } from '../../data_structures/SessionObjects';

// Mock the DAO
vi.mock('../../data_access_objects/InitializeSessionDAO', () => ({
  InitializeSessionDAO: {
    getActiveSession: vi.fn().mockResolvedValue(null),
    persist: vi.fn(),
  },
}));

// Mock logger
vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { InitializeSessionDAO } from '../../data_access_objects/InitializeSessionDAO';
import { InitializeSessionService } from '../InitializeSessionService';

const mockDAO = vi.mocked(InitializeSessionDAO);

describe('InitializeSessionService — Step 3: Validate required domain objects (Path 312)', () => {
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
    mockDAO.getActiveSession.mockResolvedValue(null);
    mockDAO.persist.mockResolvedValue(mockPersistedSession);
  });

  describe('Reachability: initialize() with invalid object → validation logic executes', () => {
    it('should execute validation when called with missing resume', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: undefined as any,
          job: validJob,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        // Validation ran and caught the missing object
        expect(e).toBeInstanceOf(SessionError);
      }
    });

    it('should execute validation when called with invalid job structure', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: { ...validJob, title: '' } as any,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
      }
    });
  });

  describe('TypeInvariant: valid objects → success; invalid → typed failure', () => {
    it('should accept valid objects and proceed to persistence', async () => {
      const result = await InitializeSessionService.createSession({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      expect(result).toBeDefined();
      expect(result.state).toBe('initialized');
    });

    it('should return MISSING_REQUIRED_OBJECT (not generic error) for missing resume', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: undefined as any,
          job: validJob,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('MISSING_REQUIRED_OBJECT');
      }
    });
  });

  describe('ErrorConsistency: missing/invalid → MISSING_REQUIRED_OBJECT with object names; DAO NOT called', () => {
    it('should throw MISSING_REQUIRED_OBJECT for missing resume and identify "ResumeObject"', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: undefined as any,
          job: validJob,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        const sessionError = e as SessionError;
        expect(sessionError.code).toBe('MISSING_REQUIRED_OBJECT');
        expect(sessionError.message).toContain('ResumeObject');
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should throw MISSING_REQUIRED_OBJECT for missing job and identify "JobObject"', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: undefined as any,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        const sessionError = e as SessionError;
        expect(sessionError.code).toBe('MISSING_REQUIRED_OBJECT');
        expect(sessionError.message).toContain('JobObject');
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should throw MISSING_REQUIRED_OBJECT for missing question and identify "QuestionObject"', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: validJob,
          question: undefined as any,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        const sessionError = e as SessionError;
        expect(sessionError.code).toBe('MISSING_REQUIRED_OBJECT');
        expect(sessionError.message).toContain('QuestionObject');
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should throw MISSING_REQUIRED_OBJECT for invalid job structure (empty title)', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: { ...validJob, title: '' },
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        const sessionError = e as SessionError;
        expect(sessionError.code).toBe('MISSING_REQUIRED_OBJECT');
        expect(sessionError.message).toContain('job');
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should throw MISSING_REQUIRED_OBJECT for invalid resume (empty content)', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: { ...validResume, content: '' },
          job: validJob,
          question: validQuestion,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        const sessionError = e as SessionError;
        expect(sessionError.code).toBe('MISSING_REQUIRED_OBJECT');
        expect(sessionError.message).toContain('resume');
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should throw MISSING_REQUIRED_OBJECT with all object names when all are null', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: null as any,
          job: null as any,
          question: null as any,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        const sessionError = e as SessionError;
        expect(sessionError.code).toBe('MISSING_REQUIRED_OBJECT');
        expect(sessionError.message).toContain('ResumeObject');
        expect(sessionError.message).toContain('JobObject');
        expect(sessionError.message).toContain('QuestionObject');
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
      expect(mockDAO.getActiveSession).not.toHaveBeenCalled();
    });
  });
});
