/**
 * route.test.ts - Step 5: API endpoint for session finalization
 *
 * TLA+ Properties:
 * - Reachability: Valid request → FinalizeSessionRequestHandler.handle() called → 200 response
 * - TypeInvariant: Response matches FinalizeSessionResponseSchema
 * - ErrorConsistency: FinalizeSessionError → proper status code; unexpected → 500
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock dependencies
vi.mock('@/server/request_handlers/FinalizeSessionRequestHandler', () => ({
  FinalizeSessionRequestHandler: {
    handle: vi.fn(),
  },
}));

import { FinalizeSessionRequestHandler } from '@/server/request_handlers/FinalizeSessionRequestHandler';
import { FinalizeSessionError } from '@/server/error_definitions/FinalizeSessionErrors';
import { HttpError } from '@/server/error_definitions/HttpErrors';
import { POST } from '../route';

const mockHandler = vi.mocked(FinalizeSessionRequestHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

function createRequest(body: Record<string, unknown> = { sessionId }): NextRequest {
  return new NextRequest(`http://localhost:3000/api/sessions/${sessionId}/finalize`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/sessions/[id]/finalize — Step 5: API endpoint', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call FinalizeSessionRequestHandler.handle() with session ID from params', async () => {
      mockHandler.handle.mockResolvedValue({
        sessionState: 'FINALIZE',
        storyRecordStatus: 'FINALIZED',
      });

      const request = createRequest();
      await POST(request, { params: Promise.resolve({ id: sessionId }) });

      expect(mockHandler.handle).toHaveBeenCalledWith(sessionId);
    });

    it('should return 200 with correct payload on success', async () => {
      mockHandler.handle.mockResolvedValue({
        sessionState: 'FINALIZE',
        storyRecordStatus: 'FINALIZED',
      });

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: sessionId }) });
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.sessionState).toBe('FINALIZE');
      expect(data.storyRecordStatus).toBe('FINALIZED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return JSON response with correct content-type', async () => {
      mockHandler.handle.mockResolvedValue({
        sessionState: 'FINALIZE',
        storyRecordStatus: 'FINALIZED',
      });

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: sessionId }) });

      expect(response.headers.get('content-type')).toContain('application/json');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 404 for SESSION_NOT_FOUND', async () => {
      mockHandler.handle.mockRejectedValue(
        new FinalizeSessionError('Session not found', 'SESSION_NOT_FOUND', 404),
      );

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: sessionId }) });
      const data = await response.json();

      expect(response.status).toBe(404);
      expect(data.code).toBe('SESSION_NOT_FOUND');
    });

    it('should return 409 for INVALID_SESSION_STATE', async () => {
      mockHandler.handle.mockRejectedValue(
        new FinalizeSessionError('Not in ACTIVE state', 'INVALID_SESSION_STATE', 409),
      );

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: sessionId }) });
      const data = await response.json();

      expect(response.status).toBe(409);
      expect(data.code).toBe('INVALID_SESSION_STATE');
    });

    it('should return 400 for VALIDATION_ERROR', async () => {
      mockHandler.handle.mockRejectedValue(
        new HttpError('Missing sessionId', 'VALIDATION_ERROR', 400),
      );

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: sessionId }) });
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Unexpected DB failure'));

      const request = createRequest();
      const response = await POST(request, { params: Promise.resolve({ id: sessionId }) });
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
