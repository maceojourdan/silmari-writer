/**
 * Tests for POST /api/sessions/initialize — Response formatting (Step 5)
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 310-initialize-new-session-with-provided-objects
 *
 * TLA+ properties tested:
 * - Reachability: mock handler+service+DAO → POST valid request → 200 with session data
 * - TypeInvariant: response matches InitializeSessionResponse schema (frontend API contract)
 * - ErrorConsistency: undefined id → SERVICE_ERROR response
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { InitializeSessionResponseSchema } from '@/server/data_structures/InitializedSession';
import type { InitializedSession } from '@/server/data_structures/InitializedSession';
import type { ResumeObject, JobObject, QuestionObject } from '@/server/data_structures/SessionObjects';

// Mock the request handler
vi.mock('@/server/request_handlers/InitializeSessionRequestHandler', () => ({
  InitializeSessionRequestHandler: {
    handle: vi.fn(),
  },
}));

import { InitializeSessionRequestHandler } from '@/server/request_handlers/InitializeSessionRequestHandler';
import { POST } from '../route';

const mockHandler = vi.mocked(InitializeSessionRequestHandler);

function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/sessions/initialize', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('POST /api/sessions/initialize — Step 5: Return session initialization response', () => {
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

  const validBody = {
    resume: validResume,
    job: validJob,
    question: validQuestion,
  };

  const mockSession: InitializedSession = {
    id: '550e8400-e29b-41d4-a716-446655440000',
    resume: validResume,
    job: validJob,
    question: validQuestion,
    state: 'initialized',
    createdAt: new Date().toISOString(),
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: full mock stack → POST → 200 with session data', () => {
    it('should return HTTP 200 with session containing id, resume, job, question, state', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.id).toBe(mockSession.id);
      expect(data.resume).toEqual(validResume);
      expect(data.job).toEqual(validJob);
      expect(data.question).toEqual(validQuestion);
      expect(data.state).toBe('initialized');
    });
  });

  describe('TypeInvariant: response matches InitializeSessionResponse schema', () => {
    it('should return response conforming to InitializeSessionResponse schema', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      const parsed = InitializeSessionResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });

    it('should include all embedded objects in response', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      // Verify embedded objects match exactly
      expect(data.resume.content).toBe(validResume.content);
      expect(data.resume.name).toBe(validResume.name);
      expect(data.resume.wordCount).toBe(validResume.wordCount);
      expect(data.job.title).toBe(validJob.title);
      expect(data.job.description).toBe(validJob.description);
      expect(data.question.text).toBe(validQuestion.text);
    });
  });

  describe('ErrorConsistency: formatting failure → SERVICE_ERROR response', () => {
    it('should return SERVICE_ERROR when session has undefined id', async () => {
      // Simulate a session with invalid id (not a UUID)
      const badSession = {
        ...mockSession,
        id: undefined as unknown as string,
      };
      mockHandler.handle.mockResolvedValue(badSession);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('SERVICE_ERROR');
    });

    it('should return standardized error for handler SessionError', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.ServiceError('Internal consistency check failed'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('SERVICE_ERROR');
      expect(data.message).toContain('Internal consistency check failed');
    });
  });
});
