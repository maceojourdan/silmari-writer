/**
 * modifySession.test.ts - Step 1: Submit modification request (API contract)
 *
 * TLA+ Properties:
 * - Reachability: mock fetch 200 → call modifySession() → POST to /api/sessions/{id}/modify
 * - TypeInvariant: request + response validated via Zod schemas
 * - ErrorConsistency: mock fetch reject → error surfaced; mock 409 → SESSION_ALREADY_FINALIZED
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 309-reject-modifications-to-finalized-session
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  ModifySessionRequestSchema,
  ModifySessionErrorResponseSchema,
  modifySession,
} from '../modifySession';

// Mock the frontend logger
vi.mock('../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { frontendLogger } from '../../logging/index';
const mockLogger = vi.mocked(frontendLogger);

// Mock global fetch
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const sessionId = '550e8400-e29b-41d4-a716-446655440000';

const successResponse = {
  id: sessionId,
  status: 'DRAFT',
  content: 'A story in progress.',
};

const errorResponse = {
  code: 'SESSION_ALREADY_FINALIZED',
  message: 'Session is already finalized and cannot be modified',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('modifySession API contract — Step 1: Submit modification request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should POST to /api/sessions/{id}/modify', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(successResponse),
      });

      await modifySession(sessionId, 'ADD_VOICE');

      expect(mockFetch).toHaveBeenCalledWith(
        `/api/sessions/${sessionId}/modify`,
        expect.objectContaining({
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
        }),
      );
    });

    it('should return parsed response on success', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(successResponse),
      });

      const result = await modifySession(sessionId, 'ADD_VOICE');

      expect(result.ok).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send request validated by ModifySessionRequestSchema', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(successResponse),
      });

      await modifySession(sessionId, 'ADD_VOICE');

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = ModifySessionRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });

    it('should validate 409 error response against ModifySessionErrorResponseSchema', () => {
      const parsed = ModifySessionErrorResponseSchema.safeParse(errorResponse);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return error result with SESSION_ALREADY_FINALIZED on 409', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 409,
        json: () => Promise.resolve(errorResponse),
      });

      const result = await modifySession(sessionId, 'ADD_VOICE');

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.code).toBe('SESSION_ALREADY_FINALIZED');
        expect(result.error.status).toBe(409);
      }
    });

    it('should call frontendLogger.error on failure', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      const result = await modifySession(sessionId, 'ADD_VOICE');

      expect(result.ok).toBe(false);
      expect(mockLogger.error).toHaveBeenCalledTimes(1);
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Session modification request failed'),
        expect.any(TypeError),
        expect.objectContaining({ action: 'modifySession' }),
      );
    });

    it('should return network error on fetch rejection', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      const result = await modifySession(sessionId, 'ADD_VOICE');

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.code).toBe('NETWORK_ERROR');
      }
    });
  });
});
