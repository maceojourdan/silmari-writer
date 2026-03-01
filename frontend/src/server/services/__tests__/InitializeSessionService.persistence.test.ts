/**
 * Tests for InitializeSessionService — prevent session persistence on validation failure
 *
 * Resource: db-h2s4 (service)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Step 4: Prevent session persistence
 *
 * TLA+ properties tested:
 * - Reachability: Trigger validation failure → assert DAO.create not called
 * - TypeInvariant: Ensure no Session entity instance created
 * - ErrorConsistency: Simulate DAO accidentally invoked after validation failure → INTERNAL_PERSISTENCE_VIOLATION
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

describe('InitializeSessionService — Step 4: Prevent session persistence (Path 312)', () => {
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

  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.getActiveSession.mockResolvedValue(null);
  });

  describe('Reachability: validation failure → DAO.create NOT called', () => {
    it('should not call DAO.persist when resume is missing', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: undefined as any,
          job: validJob,
          question: validQuestion,
        });
      } catch {
        // expected
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should not call DAO.persist when job is missing', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: null as any,
          question: validQuestion,
        });
      } catch {
        // expected
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should not call DAO.persist when question is missing', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: validResume,
          job: validJob,
          question: undefined as any,
        });
      } catch {
        // expected
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should not call DAO.persist when objects have invalid structure', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: { ...validResume, content: '' },
          job: validJob,
          question: validQuestion,
        });
      } catch {
        // expected
      }

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should not call DAO.getActiveSession when objects are missing', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: undefined as any,
          job: undefined as any,
          question: undefined as any,
        });
      } catch {
        // expected
      }

      // Should short-circuit before even checking for active sessions
      expect(mockDAO.getActiveSession).not.toHaveBeenCalled();
    });
  });

  describe('TypeInvariant: no Session entity created on validation failure', () => {
    it('should never construct a session entity when validation fails', async () => {
      try {
        await InitializeSessionService.createSession({
          resume: null as any,
          job: validJob,
          question: validQuestion,
        });
      } catch {
        // expected
      }

      // DAO.persist is the only way to create a Session entity
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });
  });

  describe('ErrorConsistency: persistence guard throws INTERNAL_PERSISTENCE_VIOLATION', () => {
    it('should expose guardPersistence that throws INTERNAL_PERSISTENCE_VIOLATION when errors present', () => {
      // The guardPersistence method is the defense-in-depth guard
      // that prevents DAO invocation if validation errors somehow bypass
      // the normal return-early check
      expect(InitializeSessionService.guardPersistence).toBeDefined();

      try {
        InitializeSessionService.guardPersistence(['ResumeObject is missing']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SessionError);
        expect((e as SessionError).code).toBe('INTERNAL_PERSISTENCE_VIOLATION');
      }
    });

    it('should NOT throw when guardPersistence is called with empty errors', () => {
      expect(() => {
        InitializeSessionService.guardPersistence([]);
      }).not.toThrow();
    });
  });
});
