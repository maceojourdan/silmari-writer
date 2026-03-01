/**
 * finalizeSession.contract.test.ts - Step 1: Submit finalize session request
 *
 * TLA+ Properties:
 * - Reachability: Call finalizeSession({ sessionId: "s1" }) → POST /api/sessions/s1/finalize
 * - TypeInvariant: Request body schema matches Zod contract { sessionId: string }
 * - ErrorConsistency: Call with {} or undefined sessionId → reject with REQUEST_VALIDATION_ERROR
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  FinalizeSessionRequestSchema,
  FinalizeSessionResponseSchema,
  finalizeSession,
} from '../finalizeSession';

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
  sessionState: 'FINALIZE',
  storyRecordStatus: 'FINALIZED',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('finalizeSession API contract — Step 1: Submit finalize session request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should POST to /api/sessions/{id}/finalize', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await finalizeSession({ sessionId });

      expect(mockFetch).toHaveBeenCalledWith(
        `/api/sessions/${sessionId}/finalize`,
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

      const result = await finalizeSession({ sessionId });

      expect(result.sessionState).toBe('FINALIZE');
      expect(result.storyRecordStatus).toBe('FINALIZED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send request body validated by FinalizeSessionRequestSchema', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await finalizeSession({ sessionId });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = FinalizeSessionRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });

    it('should validate response against FinalizeSessionResponseSchema', () => {
      const parsed = FinalizeSessionResponseSchema.safeParse(validResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject response missing required fields', () => {
      const parsed = FinalizeSessionResponseSchema.safeParse({
        sessionState: 'FINALIZE',
        // missing storyRecordStatus
      });
      expect(parsed.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should reject with REQUEST_VALIDATION_ERROR when sessionId is missing', async () => {
      await expect(
        finalizeSession({ sessionId: '' }),
      ).rejects.toMatchObject({ code: 'REQUEST_VALIDATION_ERROR' });
    });

    it('should reject with REQUEST_VALIDATION_ERROR when request is empty', async () => {
      await expect(
        finalizeSession({} as { sessionId: string }),
      ).rejects.toMatchObject({ code: 'REQUEST_VALIDATION_ERROR' });
    });

    it('should surface error to caller on fetch rejection', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      await expect(finalizeSession({ sessionId })).rejects.toThrow('Failed to fetch');
    });

    it('should call frontendLogger.error on failure', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      try {
        await finalizeSession({ sessionId });
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(1);
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Finalize session request failed'),
        expect.any(TypeError),
        expect.objectContaining({ action: 'finalizeSession' }),
      );
    });

    it('should throw on malformed response', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve({ garbage: true }),
      });

      await expect(finalizeSession({ sessionId })).rejects.toThrow('Invalid response');
    });

    it('should throw with server error message on non-ok response', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 409,
        json: () =>
          Promise.resolve({
            code: 'INVALID_SESSION_STATE',
            message: 'Session is not in ACTIVE state',
          }),
      });

      await expect(finalizeSession({ sessionId })).rejects.toThrow(
        'Session is not in ACTIVE state',
      );
    });
  });
});
