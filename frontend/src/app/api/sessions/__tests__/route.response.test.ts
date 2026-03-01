/**
 * route.response.test.ts - Step 6: Return session initialization response to frontend
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * TLA+ properties tested:
 * - Reachability: Service returns session + story → HTTP 200 with { sessionId, state: 'INIT' }
 * - TypeInvariant: Validate response against CreateSessionResponse schema
 * - ErrorConsistency: Transformation throw → 500 with INTERNAL_ERROR
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import { CreateSessionResponseSchema } from '@/server/data_structures/AnswerSession';

// Mock dependencies
vi.mock('@/server/filters/AuthAndValidationFilter', () => ({
  AuthAndValidationFilter: {
    authenticate: vi.fn(),
  },
}));

vi.mock('@/server/request_handlers/CreateSessionHandler', () => ({
  CreateSessionHandler: {
    handle: vi.fn(),
  },
}));

import { AuthAndValidationFilter } from '@/server/filters/AuthAndValidationFilter';
import { CreateSessionHandler } from '@/server/request_handlers/CreateSessionHandler';
import { HttpError } from '@/server/error_definitions/HttpErrors';
import { POST } from '../route';

const mockFilter = vi.mocked(AuthAndValidationFilter);
const mockHandler = vi.mocked(CreateSessionHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function createAuthenticatedRequest(): NextRequest {
  return new NextRequest('http://localhost:3000/api/sessions', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      'Authorization': 'Bearer valid-token',
    },
    body: JSON.stringify({}),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/sessions — Step 6: Return session initialization response', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default: auth succeeds
    mockFilter.authenticate.mockReturnValue({
      userId: 'user-abc12345',
      authenticated: true,
    });
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return HTTP 200 when service returns session + story', async () => {
      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createAuthenticatedRequest();
      const response = await POST(request);

      expect(response.status).toBe(200);
    });

    it('should return body with sessionId and state INIT', async () => {
      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(data.sessionId).toBe('550e8400-e29b-41d4-a716-446655440000');
      expect(data.state).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return response conforming to CreateSessionResponse schema', async () => {
      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      const validation = CreateSessionResponseSchema.safeParse(data);
      expect(validation.success).toBe(true);
    });

    it('should NOT include storyRecordId in response (internal detail)', async () => {
      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(data.storyRecordId).toBeUndefined();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 500 with INTERNAL_ERROR when handler throws HttpError.internal', async () => {
      mockHandler.handle.mockRejectedValue(
        new HttpError('Failed to construct valid response', 'INTERNAL_ERROR', 500),
      );

      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });

    it('should return 500 for completely unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new TypeError('Cannot read properties of undefined'));

      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
