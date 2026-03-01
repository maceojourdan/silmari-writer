/**
 * route.test.ts - Step 2: API endpoint receives session creation request
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * TLA+ properties tested:
 * - Reachability: Valid auth header → CreateSessionHandler.handle() called
 * - TypeInvariant: Parsed body conforms to CreateSessionRequest
 * - ErrorConsistency: No/invalid auth → 401 with AUTHORIZATION_ERROR
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

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
import { StoryError } from '@/server/error_definitions/StoryErrors';
import { POST } from '../route';

const mockFilter = vi.mocked(AuthAndValidationFilter);
const mockHandler = vi.mocked(CreateSessionHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function createRequest(headers: Record<string, string> = {}): NextRequest {
  return new NextRequest('http://localhost:3000/api/sessions', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      ...headers,
    },
    body: JSON.stringify({}),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/sessions — Step 2: API endpoint receives session creation request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call CreateSessionHandler.handle() when auth is valid', async () => {
      mockFilter.authenticate.mockReturnValue({
        userId: 'user-abc12345',
        authenticated: true,
      });

      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createRequest({ 'Authorization': 'Bearer valid-token' });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith({
        userId: 'user-abc12345',
      });
    });

    it('should return 200 with sessionId and state on success', async () => {
      mockFilter.authenticate.mockReturnValue({
        userId: 'user-abc12345',
        authenticated: true,
      });

      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createRequest({ 'Authorization': 'Bearer valid-token' });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.sessionId).toBe('550e8400-e29b-41d4-a716-446655440000');
      expect(data.state).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass userId from auth context to handler', async () => {
      mockFilter.authenticate.mockReturnValue({
        userId: 'user-testuser',
        authenticated: true,
      });

      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createRequest({ 'Authorization': 'Bearer test-token' });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith(
        expect.objectContaining({
          userId: 'user-testuser',
        }),
      );
    });

    it('should return JSON response with correct content-type', async () => {
      mockFilter.authenticate.mockReturnValue({
        userId: 'user-abc12345',
        authenticated: true,
      });

      mockHandler.handle.mockResolvedValue({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        storyRecordId: '550e8400-e29b-41d4-a716-446655440001',
        state: 'INIT',
      });

      const request = createRequest({ 'Authorization': 'Bearer valid-token' });
      const response = await POST(request);

      expect(response.headers.get('content-type')).toContain('application/json');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 401 with UNAUTHORIZED when auth header is missing', async () => {
      mockFilter.authenticate.mockImplementation(() => {
        throw new StoryError('Missing or empty authorization header', 'UNAUTHORIZED', 401);
      });

      const request = createRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
    });

    it('should return 401 with UNAUTHORIZED when auth header is invalid', async () => {
      mockFilter.authenticate.mockImplementation(() => {
        throw new StoryError('Invalid authorization token', 'UNAUTHORIZED', 401);
      });

      const request = createRequest({ 'Authorization': 'Bearer ' });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
    });

    it('should return 500 for unexpected errors', async () => {
      mockFilter.authenticate.mockReturnValue({
        userId: 'user-abc12345',
        authenticated: true,
      });

      mockHandler.handle.mockRejectedValue(new Error('Unexpected DB failure'));

      const request = createRequest({ 'Authorization': 'Bearer valid-token' });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
