/**
 * Tests for POST /api/session/init
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: POST valid body → handler invoked → 200 response
 * - TypeInvariant: invalid shape → 400 with SessionErrors.InvalidRequest
 * - ErrorConsistency: missing required field → structured JSON error { code, message }
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { SessionInitResult } from '@/server/data_structures/SessionObjects';

// Mock the request handler
vi.mock('@/server/request_handlers/InitSessionRequestHandler', () => ({
  InitSessionRequestHandler: {
    handle: vi.fn(),
  },
}));

import { InitSessionRequestHandler } from '@/server/request_handlers/InitSessionRequestHandler';
import { POST } from '../route';

const mockHandler = vi.mocked(InitSessionRequestHandler);

/**
 * Helper to create a NextRequest-like object for testing.
 */
function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/session/init', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('POST /api/session/init', () => {
  const validBody = {
    resume: 'Experienced software engineer with 10 years of expertise...',
    jobText: 'Senior Software Engineer at Acme Corp.',
    questionText: 'Tell me about a time you led a complex technical project.',
  };

  const mockResult: SessionInitResult = {
    sessionId: '550e8400-e29b-41d4-a716-446655440000',
    resumeId: '550e8400-e29b-41d4-a716-446655440001',
    jobId: '550e8400-e29b-41d4-a716-446655440002',
    questionId: '550e8400-e29b-41d4-a716-446655440003',
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: POST valid body → 200 response', () => {
    it('should return 200 with session IDs on success', async () => {
      mockHandler.handle.mockResolvedValue(mockResult);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.sessionId).toBe(mockResult.sessionId);
      expect(data.resumeId).toBe(mockResult.resumeId);
      expect(data.jobId).toBe(mockResult.jobId);
      expect(data.questionId).toBe(mockResult.questionId);
    });

    it('should call handler with validated payload', async () => {
      mockHandler.handle.mockResolvedValue(mockResult);

      const request = createRequest(validBody);
      await POST(request as any);

      expect(mockHandler.handle).toHaveBeenCalledWith(validBody);
    });
  });

  describe('TypeInvariant: invalid shape → 400', () => {
    it('should return 400 for missing resume', async () => {
      const request = createRequest({
        jobText: 'Some job',
        questionText: 'Some question',
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(data.message).toBeDefined();
    });

    it('should return 400 for empty resume', async () => {
      const request = createRequest({
        resume: '',
        jobText: 'Some job',
        questionText: 'Some question',
      });

      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });

    it('should return 400 for missing both jobText and jobLink', async () => {
      const request = createRequest({
        resume: 'My resume content',
        questionText: 'Some question',
      });

      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });
  });

  describe('ErrorConsistency: handler errors → structured JSON error', () => {
    it('should return SessionError status code and structured error', async () => {
      const { SessionErrors } = await import('@/server/error_definitions/SessionErrors');
      mockHandler.handle.mockRejectedValue(
        SessionErrors.ParseFailure('Cannot parse resume'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('PARSE_FAILURE');
      expect(data.message).toContain('Cannot parse resume');
    });

    it('should return GenericError status code for unexpected errors', async () => {
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
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
