/**
 * Integration test for the session initialization path
 *
 * Path: 294-parse-and-store-session-input-objects
 *
 * This proves end-to-end:
 * - Reachability: Trigger → Endpoint → Handler → Processor → Service → DAO → Response
 * - TypeInvariant: All boundary schemas validated via Zod
 * - ErrorConsistency: All defined error branches return standardized error objects
 *
 * Note: Mocks only the DAO layer (database boundary). Everything above
 * runs with real implementations: transformer, verifier, processor, service, handler.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { z } from 'zod';

// Only mock the DAO — everything else is real
vi.mock('../data_access_objects/SessionInitDAO', () => ({
  SessionInitDAO: {
    insertResume: vi.fn(),
    insertJob: vi.fn(),
    insertQuestion: vi.fn(),
    insertSession: vi.fn(),
  },
}));

import { SessionInitDAO } from '../data_access_objects/SessionInitDAO';
import { InitSessionRequestHandler } from '../request_handlers/InitSessionRequestHandler';
import { validateSessionInitInput } from '@/verifiers/SessionInitVerifier';
import { InitSessionResponseSchema } from '@/api_contracts/initSession';

const mockDAO = vi.mocked(SessionInitDAO);

describe('Session Initialization Integration', () => {
  const validInput = {
    resume: 'Experienced software engineer with 10 years of expertise in building distributed systems. Proficient in TypeScript, Python, and Go. Led teams of 5-10 engineers across multiple product launches.',
    jobText: 'Senior Software Engineer at Acme Corp. We are looking for an experienced engineer to lead our distributed systems team. Requirements: 8+ years experience, TypeScript, cloud infrastructure.',
    questionText: 'Tell me about a time you led a complex technical project and how you handled challenges along the way.',
  };

  const mockResumeId = '550e8400-e29b-41d4-a716-446655440001';
  const mockJobId = '550e8400-e29b-41d4-a716-446655440002';
  const mockQuestionId = '550e8400-e29b-41d4-a716-446655440003';
  const mockSessionId = '550e8400-e29b-41d4-a716-446655440000';

  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.insertResume.mockResolvedValue(mockResumeId);
    mockDAO.insertJob.mockResolvedValue(mockJobId);
    mockDAO.insertQuestion.mockResolvedValue(mockQuestionId);
    mockDAO.insertSession.mockResolvedValue(mockSessionId);
  });

  describe('Reachability: Full path from input to persisted result', () => {
    it('should validate input, transform, verify, persist, and return IDs', async () => {
      // Step 1: Frontend validation
      const validation = validateSessionInitInput(validInput);
      expect(validation.success).toBe(true);

      if (!validation.success) return;

      // Steps 2-5: Handler orchestrates everything
      const result = await InitSessionRequestHandler.handle(validation.data);

      // Assert: IDs returned
      expect(result.sessionId).toBe(mockSessionId);
      expect(result.resumeId).toBe(mockResumeId);
      expect(result.jobId).toBe(mockJobId);
      expect(result.questionId).toBe(mockQuestionId);

      // Assert: DAO was called with structured objects
      expect(mockDAO.insertResume).toHaveBeenCalledTimes(1);
      const resumeArg = mockDAO.insertResume.mock.calls[0][0];
      expect(resumeArg.content).toBe(validInput.resume);
      expect(resumeArg.wordCount).toBeGreaterThan(0);

      expect(mockDAO.insertJob).toHaveBeenCalledTimes(1);
      const jobArg = mockDAO.insertJob.mock.calls[0][0];
      expect(jobArg.sourceType).toBe('text');
      expect(jobArg.description).toBe(validInput.jobText);

      expect(mockDAO.insertQuestion).toHaveBeenCalledTimes(1);
      const questionArg = mockDAO.insertQuestion.mock.calls[0][0];
      expect(questionArg.text).toBe(validInput.questionText);

      expect(mockDAO.insertSession).toHaveBeenCalledTimes(1);
      const sessionArg = mockDAO.insertSession.mock.calls[0][0];
      expect(sessionArg.resumeId).toBe(mockResumeId);
      expect(sessionArg.jobId).toBe(mockJobId);
      expect(sessionArg.questionId).toBe(mockQuestionId);
      expect(sessionArg.status).toBe('INITIALIZED');
    });

    it('should work with job link instead of job text', async () => {
      const linkInput = {
        resume: 'My professional resume with engineering experience.',
        jobLink: 'https://careers.acme.com/senior-engineer-123',
        questionText: 'Describe your approach to system design.',
      };

      const validation = validateSessionInitInput(linkInput);
      expect(validation.success).toBe(true);

      if (!validation.success) return;

      const result = await InitSessionRequestHandler.handle(validation.data);

      expect(result.sessionId).toBe(mockSessionId);
      const jobArg = mockDAO.insertJob.mock.calls[0][0];
      expect(jobArg.sourceType).toBe('link');
      expect(jobArg.sourceValue).toBe(linkInput.jobLink);
    });
  });

  describe('TypeInvariant: Response matches InitSessionResponseSchema', () => {
    it('should produce a response conforming to the API contract', async () => {
      const validation = validateSessionInitInput(validInput);
      if (!validation.success) return;

      const result = await InitSessionRequestHandler.handle(validation.data);

      const parsed = InitSessionResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: Error paths return standardized errors', () => {
    it('should reject invalid input at the validation layer', () => {
      const invalidInput = {
        resume: '',
        questionText: '',
      };

      const validation = validateSessionInitInput(invalidInput);
      expect(validation.success).toBe(false);
      if (!validation.success) {
        expect(validation.errors.length).toBeGreaterThan(0);
      }
    });

    it('should throw PERSISTENCE_FAILURE when DAO fails', async () => {
      mockDAO.insertResume.mockRejectedValue(new Error('Connection refused'));

      const validation = validateSessionInitInput(validInput);
      if (!validation.success) return;

      try {
        await InitSessionRequestHandler.handle(validation.data);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('PERSISTENCE_FAILURE');
        expect(e.statusCode).toBe(500);
        expect(e.retryable).toBe(true);
      }
    });

    it('should throw PARSE_FAILURE when transformer encounters whitespace-only input', async () => {
      // Whitespace-only resume passes validation (min(1) checks length, not content)
      // but the transformer catches it during trim → ParseFailure
      const whitespaceInput = {
        resume: '   ', // passes min(1) but empty after trim
        jobText: 'Some job',
        questionText: 'Some question',
      };

      // Validation passes (3 chars > 0)
      const validation = validateSessionInitInput(whitespaceInput);
      expect(validation.success).toBe(true);

      if (!validation.success) return;

      // Handler catches transformer's error → PARSE_FAILURE
      try {
        await InitSessionRequestHandler.handle(validation.data);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('PARSE_FAILURE');
        expect(e.statusCode).toBe(422);
      }
    });
  });
});
