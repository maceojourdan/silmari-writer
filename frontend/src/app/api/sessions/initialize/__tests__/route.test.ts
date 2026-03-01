/**
 * Tests for POST /api/sessions/initialize
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 310-initialize-new-session-with-provided-objects
 *
 * TLA+ properties tested:
 * - Reachability: POST valid body → handler invoked → 200 response
 * - TypeInvariant: request body parsed into typed objects using Zod
 * - ErrorConsistency: POST with missing resume → 400, matches BackendError.validation shape
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

/**
 * Helper to create a NextRequest-like object for testing.
 */
function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/sessions/initialize', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('POST /api/sessions/initialize — Step 1: Receive session initialization request', () => {
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

  describe('Reachability: POST valid body → handler invoked → 200 response', () => {
    it('should return 200 with session data on success', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.id).toBe(mockSession.id);
      expect(data.state).toBe('initialized');
    });

    it('should call handler with structured payload', async () => {
      mockHandler.handle.mockResolvedValue(mockSession);

      const request = createRequest(validBody);
      await POST(request as any);

      expect(mockHandler.handle).toHaveBeenCalledTimes(1);
      const handlerArg = mockHandler.handle.mock.calls[0][0];
      expect(handlerArg.resume).toEqual(validResume);
      expect(handlerArg.job).toEqual(validJob);
      expect(handlerArg.question).toEqual(validQuestion);
    });
  });

  describe('TypeInvariant: request body parsed into typed objects using Zod', () => {
    it('should return 400 for missing resume object', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(data.message).toBeDefined();
    });

    it('should return 400 for missing job object', async () => {
      const request = createRequest({
        resume: validResume,
        question: validQuestion,
      });

      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });

    it('should return 400 for missing question object', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
      });

      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });
  });

  describe('ErrorConsistency: errors → structured JSON error { code, message }', () => {
    it('should return SessionError status code and structured error', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.ValidationFailure('Question text is empty'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('VALIDATION_FAILURE');
      expect(data.message).toContain('Question text is empty');
    });

    it('should return GenericError status code for internal errors', async () => {
      const { GenericErrors } = await import('@/server/error_definitions/GenericErrors');
      mockHandler.handle.mockRejectedValue(
        GenericErrors.InternalError('Something broke'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });

    it('should return 500 for completely unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Runtime crash'));

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('GENERIC_USER_ERROR');
    });
  });
});
