/**
 * Integration test for Path 310: initialize-new-session-with-provided-objects
 *
 * Terminal Condition: Exercises the full path end-to-end:
 *   POST /api/sessions/initialize → RequestHandler → Service → DAO
 *
 * Proves:
 * - Reachability: Trigger exercises entire chain
 * - TypeInvariant: Objects preserved end-to-end
 * - ErrorConsistency: All error branches tested independently in unit tests
 *
 * The DAO is mocked to simulate Supabase persistence. All other layers
 * run their real implementations to verify integration.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { InitializeSessionResponseSchema } from '@/server/data_structures/InitializedSession';
import type { ResumeObject, JobObject, QuestionObject } from '@/server/data_structures/SessionObjects';

// Mock ONLY the DAO (lowest layer) to simulate DB
vi.mock('@/server/data_access_objects/InitializeSessionDAO', () => {
  return {
    InitializeSessionDAO: {
      getActiveSession: vi.fn().mockResolvedValue(null),
      persist: vi.fn().mockImplementation(async (session: any) => ({
        id: '550e8400-e29b-41d4-a716-446655440000',
        resume: session.resume,
        job: session.job,
        question: session.question,
        state: session.state,
        createdAt: session.createdAt,
      })),
    },
  };
});

// Mock logger to avoid noisy output
vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { InitializeSessionDAO } from '@/server/data_access_objects/InitializeSessionDAO';
import { POST } from '@/app/api/sessions/initialize/route';

const mockDAO = vi.mocked(InitializeSessionDAO);

function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/sessions/initialize', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('Path 310 Integration: initialize-new-session-with-provided-objects', () => {
  const validResume: ResumeObject = {
    content: 'Experienced software engineer with 10 years of expertise in TypeScript and React.',
    name: 'Jane Smith Resume',
    wordCount: 12,
  };

  const validJob: JobObject = {
    title: 'Senior Software Engineer',
    description: 'We are looking for a senior engineer to lead our frontend team building next-gen applications.',
    sourceType: 'text',
    sourceValue: 'We are looking for a senior engineer to lead our frontend team building next-gen applications.',
  };

  const validQuestion: QuestionObject = {
    text: 'Tell me about a time you led a complex technical project and how you handled technical disagreements.',
  };

  beforeEach(() => {
    vi.clearAllMocks();

    // Reset DAO mocks for each test
    mockDAO.getActiveSession.mockResolvedValue(null);
    mockDAO.persist.mockImplementation(async (session: any) => ({
      id: '550e8400-e29b-41d4-a716-446655440000',
      resume: session.resume,
      job: session.job,
      question: session.question,
      state: session.state,
      createdAt: session.createdAt,
    }));
  });

  describe('Reachability: full path exercises entire chain', () => {
    it('should return 200 with initialized session for valid request', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.state).toBe('initialized');
      expect(data.id).toBeDefined();
    });

    it('should call DAO.persist exactly once', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      await POST(request as any);

      expect(mockDAO.persist).toHaveBeenCalledTimes(1);
    });
  });

  describe('TypeInvariant: embedded objects preserved end-to-end', () => {
    it('should preserve ResumeObject exactly in response', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.resume.content).toBe(validResume.content);
      expect(data.resume.name).toBe(validResume.name);
      expect(data.resume.wordCount).toBe(validResume.wordCount);
    });

    it('should preserve JobObject exactly in response', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.job.title).toBe(validJob.title);
      expect(data.job.description).toBe(validJob.description);
      expect(data.job.sourceType).toBe(validJob.sourceType);
      expect(data.job.sourceValue).toBe(validJob.sourceValue);
    });

    it('should preserve QuestionObject exactly in response', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.question.text).toBe(validQuestion.text);
    });

    it('should return response conforming to InitializeSessionResponse schema', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      const parsed = InitializeSessionResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: validation errors from real handler layer', () => {
    it('should return 400 for missing resume (caught at endpoint layer)', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should return 400 for empty question text (caught at endpoint layer)', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: { text: '' },
      });

      const response = await POST(request as any);

      expect(response.status).toBe(400);
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should return 500 when DAO throws persistence error', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockDAO.persist.mockRejectedValue(
        SessionErrors.PersistenceFailure('Connection refused'),
      );

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('PERSISTENCE_FAILURE');
    });
  });
});
