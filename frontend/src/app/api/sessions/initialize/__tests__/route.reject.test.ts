/**
 * Tests for POST /api/sessions/initialize — rejection path
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Step 1: Receive session initialization request
 *
 * TLA+ properties tested:
 * - Reachability: Send valid JSON body → handler is invoked (mock SessionInitHandler.handle)
 * - TypeInvariant: Parsed body matches SessionInitRequest type; handler receives typed objects
 * - ErrorConsistency: Send malformed JSON → 400 + INVALID_REQUEST_FORMAT; handler not called
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
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

function createRawRequest(rawBody: string): Request {
  return new Request('http://localhost/api/sessions/initialize', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: rawBody,
  });
}

describe('POST /api/sessions/initialize — Step 1: Rejection path (Path 312)', () => {
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

  describe('Reachability: valid JSON → handler invoked, 4xx NOT returned', () => {
    it('should invoke handler when body is valid', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);

      expect(mockHandler.handle).toHaveBeenCalledTimes(1);
      expect(response.status).not.toBeGreaterThanOrEqual(400);
    });

    it('should pass structured payload to handler', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      await POST(request as any);

      const handlerArg = mockHandler.handle.mock.calls[0][0];
      expect(handlerArg).toEqual({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });
    });
  });

  describe('TypeInvariant: parsed body matches SessionInitRequest type', () => {
    it('should deliver typed { resume, job, question } to handler', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      await POST(request as any);

      const handlerArg = mockHandler.handle.mock.calls[0][0];
      expect(handlerArg).toHaveProperty('resume');
      expect(handlerArg).toHaveProperty('job');
      expect(handlerArg).toHaveProperty('question');
      expect(handlerArg.resume.content).toBe(validResume.content);
      expect(handlerArg.job.title).toBe(validJob.title);
      expect(handlerArg.question.text).toBe(validQuestion.text);
    });
  });

  describe('ErrorConsistency: malformed/missing data → INVALID_REQUEST_FORMAT, handler NOT called', () => {
    it('should return 400 with INVALID_REQUEST_FORMAT for completely missing body fields', async () => {
      const request = createRequest({});

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 with INVALID_REQUEST_FORMAT for missing resume', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(data.message).toBeDefined();
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 with INVALID_REQUEST_FORMAT for missing job', async () => {
      const request = createRequest({
        resume: validResume,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 with INVALID_REQUEST_FORMAT for missing question', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 with INVALID_REQUEST_FORMAT for invalid JSON string', async () => {
      const request = createRawRequest('not valid json{{{');

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should include error details in message for missing fields', async () => {
      const request = createRequest({
        resume: validResume,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.message).toBeDefined();
      expect(typeof data.message).toBe('string');
    });
  });
});
