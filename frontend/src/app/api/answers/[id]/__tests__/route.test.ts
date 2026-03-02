/**
 * route.test.ts - PUT /api/answers/[id]
 *
 * TLA+ Properties:
 * - Reachability: Valid PUT with auth and { content } → handler invoked, 200 returned
 * - TypeInvariant: Missing content → 400 VALIDATION_ERROR; empty content → 400 VALIDATION_ERROR
 * - ErrorConsistency:
 *     - Missing auth → 401 UNAUTHORIZED
 *     - Handler throws LOCKED_ANSWER_MODIFICATION_FORBIDDEN → 403
 *     - Handler throws ANSWER_NOT_FOUND → 404
 *     - Handler throws generic Error → 500 INTERNAL_ERROR
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 337-prevent-edit-of-locked-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('@/server/request_handlers/UpdateAnswerRequestHandler', () => ({
  UpdateAnswerRequestHandler: {
    handle: vi.fn(),
  },
}));

import { UpdateAnswerRequestHandler } from '@/server/request_handlers/UpdateAnswerRequestHandler';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';
import { PUT } from '../route';

const mockHandler = vi.mocked(UpdateAnswerRequestHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

function createRequest(
  body: unknown,
  headers: Record<string, string> = {
    'Content-Type': 'application/json',
    Authorization: 'Bearer test-token',
  },
): NextRequest {
  return new NextRequest(`http://localhost/api/answers/${answerId}`, {
    method: 'PUT',
    headers,
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('PUT /api/answers/[id] — Path 337: Prevent Edit of Locked Answer', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call UpdateAnswerRequestHandler.handle with id and content', async () => {
      mockHandler.handle.mockResolvedValue({
        id: answerId,
        content: 'updated',
      });

      const request = createRequest({ content: 'updated' });
      await PUT(request, { params: Promise.resolve({ id: answerId }) });

      expect(mockHandler.handle).toHaveBeenCalledWith(answerId, 'updated');
    });

    it('should return 200 with correct payload on success', async () => {
      mockHandler.handle.mockResolvedValue({
        id: answerId,
        content: 'updated',
      });

      const request = createRequest({ content: 'updated' });
      const response = await PUT(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.id).toBe(answerId);
      expect(data.content).toBe('updated');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return 400 VALIDATION_ERROR when content is missing from body', async () => {
      const request = createRequest({});
      const response = await PUT(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });

    it('should return 400 VALIDATION_ERROR when content is empty string', async () => {
      const request = createRequest({ content: '' });
      const response = await PUT(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 401 UNAUTHORIZED when authorization header is missing', async () => {
      const request = createRequest(
        { content: 'updated' },
        { 'Content-Type': 'application/json' },
      );
      const response = await PUT(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
    });

    it('should return 403 for LOCKED_ANSWER_MODIFICATION_FORBIDDEN errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new AnswerError(
          'This answer has been finalized and cannot be modified.',
          'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
          403,
        ),
      );

      const request = createRequest({ content: 'updated' });
      const response = await PUT(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(403);
      expect(data.code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
    });

    it('should return 404 for ANSWER_NOT_FOUND errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new AnswerError('Answer not found', 'ANSWER_NOT_FOUND', 404),
      );

      const request = createRequest({ content: 'updated' });
      const response = await PUT(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(404);
      expect(data.code).toBe('ANSWER_NOT_FOUND');
    });

    it('should return 500 INTERNAL_ERROR for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Unexpected DB failure'));

      const request = createRequest({ content: 'updated' });
      const response = await PUT(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
