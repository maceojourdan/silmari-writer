/**
 * Tests for POST /api/sessions/initialize — Error Response (Step 4)
 *
 * Resource: api-m5g7 (endpoint), api-n8k2 (request_handler)
 * Path: 311-reject-duplicate-session-initialization
 *
 * TLA+ properties tested:
 * - Reachability: Mock service throws SESSION_ALREADY_ACTIVE → endpoint returns HTTP 409
 * - TypeInvariant: Response JSON matches SessionInitErrorResponse type { error: { code, message } }
 * - ErrorConsistency: Unexpected transformation error → HTTP 500 with SYSTEM_ERROR
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
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

describe('POST /api/sessions/initialize — Step 4: Return error response to client', () => {
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

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: SESSION_ALREADY_ACTIVE → HTTP 409 (Conflict)', () => {
    it('should return HTTP 409 when handler throws SESSION_ALREADY_ACTIVE', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.SessionAlreadyActive(),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);

      expect(response.status).toBe(409);
    });
  });

  describe('TypeInvariant: response matches SessionInitErrorResponse type', () => {
    it('should return error response with { code, message } shape', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.SessionAlreadyActive(),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(data).toHaveProperty('code');
      expect(data).toHaveProperty('message');
      expect(data.code).toBe('SESSION_ALREADY_ACTIVE');
      expect(typeof data.message).toBe('string');
      expect(data.message.length).toBeGreaterThan(0);
    });

    it('should return VALIDATION_FAILURE with 422 for validation errors', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.ValidationFailure('Missing required field'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('VALIDATION_FAILURE');
    });
  });

  describe('ErrorConsistency: transformation failures → HTTP 500', () => {
    it('should return HTTP 500 with INTERNAL_ERROR for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new Error('Unexpected crash during error transformation'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });

    it('should return HTTP 500 with GenericError code for generic errors', async () => {
      const { GenericErrors } = await import('@/server/error_definitions/GenericErrors');
      mockHandler.handle.mockRejectedValue(
        GenericErrors.InternalError('Internal processing failure'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
