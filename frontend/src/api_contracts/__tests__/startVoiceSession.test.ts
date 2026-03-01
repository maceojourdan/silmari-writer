/**
 * startVoiceSession.test.ts - Step 3: Submit Session Start with Consent Flag
 *
 * TLA+ Properties:
 * - Reachability: call contract with { consent: true } → POST to /api/voice-session/start
 * - TypeInvariant: payload validated via Zod schema; consent must be literal true
 * - ErrorConsistency: Mock network failure → retry logic triggered (max 2);
 *                     After 2 failures → log error and expose retry UI state
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  StartVoiceSessionRequestSchema,
  StartVoiceSessionResponseSchema,
  startVoiceSession,
} from '../startVoiceSession';

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

const validResponse = {
  sessionStatus: 'INIT',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('startVoiceSession API contract — Step 3: Submit Session Start with Consent Flag', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should POST to /api/voice-session/start with consent: true', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await startVoiceSession({ consent: true });

      expect(mockFetch).toHaveBeenCalledWith(
        '/api/voice-session/start',
        expect.objectContaining({
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
        }),
      );
    });

    it('should send consent: true in the request body', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await startVoiceSession({ consent: true });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      expect(body.consent).toBe(true);
    });

    it('should return parsed response on success', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      const result = await startVoiceSession({ consent: true });

      expect(result.sessionStatus).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate request with consent: true against schema', () => {
      const parsed = StartVoiceSessionRequestSchema.safeParse({ consent: true });
      expect(parsed.success).toBe(true);
    });

    it('should reject request with consent: false against schema', () => {
      const parsed = StartVoiceSessionRequestSchema.safeParse({ consent: false });
      expect(parsed.success).toBe(false);
    });

    it('should reject request with missing consent field', () => {
      const parsed = StartVoiceSessionRequestSchema.safeParse({});
      expect(parsed.success).toBe(false);
    });

    it('should reject request with consent: "yes" (non-boolean)', () => {
      const parsed = StartVoiceSessionRequestSchema.safeParse({ consent: 'yes' });
      expect(parsed.success).toBe(false);
    });

    it('should validate response against StartVoiceSessionResponseSchema', () => {
      const parsed = StartVoiceSessionResponseSchema.safeParse(validResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject response missing sessionStatus', () => {
      const parsed = StartVoiceSessionResponseSchema.safeParse({});
      expect(parsed.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should retry on first network failure and succeed on second attempt', async () => {
      mockFetch
        .mockRejectedValueOnce(new TypeError('Failed to fetch'))
        .mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve(validResponse),
        });

      const result = await startVoiceSession({ consent: true });

      expect(mockFetch).toHaveBeenCalledTimes(2);
      expect(result.sessionStatus).toBe('INIT');
    });

    it('should retry twice and throw on third failure', async () => {
      mockFetch
        .mockRejectedValueOnce(new TypeError('Failed to fetch'))
        .mockRejectedValueOnce(new TypeError('Failed to fetch'))
        .mockRejectedValueOnce(new TypeError('Failed to fetch'));

      await expect(startVoiceSession({ consent: true })).rejects.toThrow('Failed to fetch');
      expect(mockFetch).toHaveBeenCalledTimes(3); // initial + 2 retries
    });

    it('should call frontendLogger.error after all retries exhausted', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      try {
        await startVoiceSession({ consent: true });
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(1);
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Voice session start request failed'),
        expect.any(TypeError),
        expect.objectContaining({ action: 'startVoiceSession' }),
      );
    });

    it('should throw on malformed response', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve({ garbage: true }),
      });

      await expect(startVoiceSession({ consent: true })).rejects.toThrow('Invalid response');
    });

    it('should throw with server error message on non-ok response', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 400,
        json: () =>
          Promise.resolve({
            code: 'CONSENT_REQUIRED',
            message: 'Affirmative consent is required before starting voice session',
          }),
      });

      await expect(startVoiceSession({ consent: true })).rejects.toThrow(
        'Affirmative consent is required before starting voice session',
      );
    });
  });
});
