/**
 * route.test.ts - Step 2: Handle Finalize API Request
 *
 * TLA+ Properties:
 * - Reachability: POST /api/answers/:id/finalize with valid auth → processor invoked and 200 returned
 * - TypeInvariant: Invalid body (missing id) → 400 with validation error
 * - ErrorConsistency: Missing/invalid auth → 401 with FinalizeAnswerErrors.UNAUTHORIZED
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 333-finalize-answer-locks-editing
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock dependencies
vi.mock('@/server/request_handlers/FinalizeAnswerRequestHandler', () => ({
  FinalizeAnswerRequestHandler: {
    handle: vi.fn(),
  },
}));

import { FinalizeAnswerRequestHandler } from '@/server/request_handlers/FinalizeAnswerRequestHandler';
import { FinalizeAnswerError } from '@/server/error_definitions/FinalizeAnswerErrors';
import { POST } from '../route';

const mockHandler = vi.mocked(FinalizeAnswerRequestHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

function createRequest(
  headers: Record<string, string> = { 'Content-Type': 'application/json', 'Authorization': 'Bearer test-token-12345678' },
): NextRequest {
  return new NextRequest(`http://localhost:3000/api/answers/${answerId}/finalize`, {
    method: 'POST',
    headers,
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/answers/[id]/finalize — Step 2: Handle Finalize API Request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call FinalizeAnswerRequestHandler.handle() with answer ID from params', async () => {
      mockHandler.handle.mockResolvedValue({
        id: answerId,
        finalized: true,
        editable: false,
      });

      const request = createRequest();
      await POST(request, { params: Promise.resolve({ id: answerId }) });

      expect(mockHandler.handle).toHaveBeenCalledWith(answerId);
    });

    it('should return 200 with correct payload on success', async () => {
      mockHandler.handle.mockResolvedValue({
        id: answerId,
        finalized: true,
        editable: false,
      });

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.id).toBe(answerId);
      expect(data.finalized).toBe(true);
      expect(data.editable).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return 400 when answer ID is missing from params', async () => {
      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: '' }) });
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });

    it('should return JSON response with correct content-type', async () => {
      mockHandler.handle.mockResolvedValue({
        id: answerId,
        finalized: true,
        editable: false,
      });

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: answerId }) });

      expect(response.headers.get('content-type')).toContain('application/json');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 401 when authorization header is missing', async () => {
      const request = createRequest({ 'Content-Type': 'application/json' });
      const response = await POST(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
    });

    it('should return 404 for ANSWER_NOT_FOUND errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new FinalizeAnswerError('Answer not found', 'ANSWER_NOT_FOUND', 404),
      );

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(404);
      expect(data.code).toBe('ANSWER_NOT_FOUND');
    });

    it('should return 409 for ANSWER_ALREADY_FINALIZED errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new FinalizeAnswerError('Already finalized', 'ANSWER_ALREADY_FINALIZED', 409),
      );

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(409);
      expect(data.code).toBe('ANSWER_ALREADY_FINALIZED');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Unexpected DB failure'));

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
