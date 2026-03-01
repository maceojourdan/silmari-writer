/**
 * approveSession.test.ts - Step 2: Invoke Approval Endpoint
 *
 * TLA+ Properties:
 * - Reachability: Mock fetch 200 → call approveSession() → POST to /api/sessions/{id}/approve
 * - TypeInvariant: Request + response validated via Zod schemas
 * - ErrorConsistency: Mock fetch reject → error surfaced to caller → clientLogger.error called → no UI state mutation
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  ApproveSessionRequestSchema,
  ApproveSessionResponseSchema,
  approveSession,
} from '../approveSession';

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

const validResponse = {
  id: sessionId,
  state: 'FINALIZE',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('approveSession API contract — Step 2: Invoke Approval Endpoint', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should POST to /api/sessions/{id}/approve', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await approveSession(sessionId);

      expect(mockFetch).toHaveBeenCalledWith(
        `/api/sessions/${sessionId}/approve`,
        expect.objectContaining({
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
        }),
      );
    });

    it('should return parsed response on success', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      const result = await approveSession(sessionId);

      expect(result.id).toBe(sessionId);
      expect(result.state).toBe('FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send request validated by ApproveSessionRequestSchema', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await approveSession(sessionId);

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = ApproveSessionRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });

    it('should validate response against ApproveSessionResponseSchema', () => {
      const parsed = ApproveSessionResponseSchema.safeParse(validResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject response missing required fields', () => {
      const parsed = ApproveSessionResponseSchema.safeParse({
        id: sessionId,
        // missing state, createdAt, updatedAt
      });
      expect(parsed.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should surface error to caller on fetch rejection', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      await expect(approveSession(sessionId)).rejects.toThrow('Failed to fetch');
    });

    it('should call clientLogger.error on failure', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      try {
        await approveSession(sessionId);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(1);
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Session approval request failed'),
        expect.any(TypeError),
        expect.objectContaining({ action: 'approveSession' }),
      );
    });

    it('should throw on malformed response', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve({ garbage: true }),
      });

      await expect(approveSession(sessionId)).rejects.toThrow('Invalid response');
    });

    it('should throw with server error message on non-ok response', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 409,
        json: () =>
          Promise.resolve({
            code: 'INVALID_STATE_TRANSITION',
            message: 'Cannot transition from FINALIZE to FINALIZE',
          }),
      });

      await expect(approveSession(sessionId)).rejects.toThrow(
        'Cannot transition from FINALIZE to FINALIZE',
      );
    });
  });
});
