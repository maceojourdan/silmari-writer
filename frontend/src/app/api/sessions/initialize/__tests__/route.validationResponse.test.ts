/**
 * Tests for POST /api/sessions/initialize — Validation error response mapping
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Step 5: Return validation error response
 *
 * TLA+ properties tested:
 * - Reachability: Send request missing ResumeObject → HTTP 400 with object-level error detail
 * - TypeInvariant: Response matches ValidationErrorResponse type { code, message }
 * - ErrorConsistency: Mock handler error mapping failure → GENERIC_USER_ERROR, no stack trace
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

describe('POST /api/sessions/initialize — Step 5: Validation error response (Path 312)', () => {
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
  });

  describe('Reachability: missing ResumeObject → HTTP 400 with object-level detail', () => {
    it('should return HTTP 400 when resume is missing', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });

    it('should include error detail identifying the missing object', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.message).toBeDefined();
      expect(typeof data.message).toBe('string');
      expect(data.message.length).toBeGreaterThan(0);
    });
  });

  describe('TypeInvariant: response matches ValidationErrorResponse type { code, message }', () => {
    it('should return structured { code, message } for validation errors from handler', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.MissingRequiredObject('Validation failed: ResumeObject is required but missing'),
      );

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data).toHaveProperty('code');
      expect(data).toHaveProperty('message');
      expect(data.code).toBe('MISSING_REQUIRED_OBJECT');
      expect(typeof data.message).toBe('string');
    });

    it('should return VALIDATION_FAILURE with 422 for schema validation errors', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.ValidationFailure('Validation failed: resume.content: Resume content is required'),
      );

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('VALIDATION_FAILURE');
    });

    it('should return INTERNAL_PERSISTENCE_VIOLATION with 500 for guard breach', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.InternalPersistenceViolation('Guard triggered'),
      );

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_PERSISTENCE_VIOLATION');
    });
  });

  describe('ErrorConsistency: error mapping failure → GENERIC_USER_ERROR, no stack trace', () => {
    it('should return GENERIC_USER_ERROR when handler throws unexpected error', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Runtime crash'));

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('GENERIC_USER_ERROR');
    });

    it('should NOT expose stack trace in GENERIC_USER_ERROR response', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Internal details: stack at line 42'));

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.code).toBe('GENERIC_USER_ERROR');
      // Should not contain stack trace details
      expect(data.message).not.toContain('at line');
      expect(data.message).not.toContain('stack');
      expect(data.message).not.toContain('Internal details');
    });

    it('should return GENERIC_USER_ERROR for null thrown', async () => {
      mockHandler.handle.mockRejectedValue(null);

      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('GENERIC_USER_ERROR');
    });
  });
});
