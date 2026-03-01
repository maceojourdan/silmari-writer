/**
 * finalize.test.ts - Step 1: Invoke Finalize Endpoint
 *
 * TLA+ Properties:
 * - Reachability: Call finalizeDraft({ draftId, userId }) → POST to /api/finalize
 * - TypeInvariant: Zod schema validates { draftId: string, userId: string }; response matches FinalizeResponse
 * - ErrorConsistency: Call with { draftId: "" } → SharedErrors.MalformedRequest
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  FinalizeRequestSchema,
  FinalizeResponseSchema,
  finalizeDraft,
} from '../finalize';

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

const draftId = '660e8400-e29b-41d4-a716-446655440001';
const userId = '770e8400-e29b-41d4-a716-446655440002';

const validResponse = {
  artifact: {
    draftId,
    content: 'Finalized content here',
    title: 'My Draft',
    exportedAt: '2026-02-28T12:02:00.000Z',
    format: 'text',
    metadata: {
      userId,
      originalCreatedAt: '2026-02-28T10:00:00.000Z',
      finalizedAt: '2026-02-28T12:02:00.000Z',
    },
  },
  finalized: true,
  metricsLogged: true,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('finalizeDraft API contract — Step 1: Invoke Finalize Endpoint', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should POST to /api/finalize', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await finalizeDraft({ draftId, userId });

      expect(mockFetch).toHaveBeenCalledWith(
        '/api/finalize',
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

      const result = await finalizeDraft({ draftId, userId });

      expect(result.finalized).toBe(true);
      expect(result.metricsLogged).toBe(true);
      expect(result.artifact.draftId).toBe(draftId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send request body validated by FinalizeRequestSchema', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await finalizeDraft({ draftId, userId });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = FinalizeRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });

    it('should validate response against FinalizeResponseSchema', () => {
      const parsed = FinalizeResponseSchema.safeParse(validResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject response missing required fields', () => {
      const parsed = FinalizeResponseSchema.safeParse({
        artifact: { draftId },
        // missing finalized, metricsLogged
      });
      expect(parsed.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw MalformedRequest error when draftId is empty', async () => {
      await expect(finalizeDraft({ draftId: '', userId })).rejects.toThrow(
        'MALFORMED_REQUEST',
      );
    });

    it('should throw MalformedRequest error when userId is empty', async () => {
      await expect(finalizeDraft({ draftId, userId: '' })).rejects.toThrow(
        'MALFORMED_REQUEST',
      );
    });

    it('should surface error to caller on fetch rejection', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      await expect(finalizeDraft({ draftId, userId })).rejects.toThrow(
        'Failed to fetch',
      );
    });

    it('should call frontendLogger.error on failure', async () => {
      mockFetch.mockRejectedValue(new TypeError('Failed to fetch'));

      try {
        await finalizeDraft({ draftId, userId });
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(1);
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Finalize request failed'),
        expect.any(TypeError),
        expect.objectContaining({ action: 'finalizeDraft' }),
      );
    });

    it('should throw on malformed response', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve({ garbage: true }),
      });

      await expect(finalizeDraft({ draftId, userId })).rejects.toThrow(
        'Invalid response',
      );
    });

    it('should throw with server error message on non-ok response', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 422,
        json: () =>
          Promise.resolve({
            code: 'INVALID_DRAFT_STATE',
            message: 'Draft is not in APPROVED state',
          }),
      });

      await expect(finalizeDraft({ draftId, userId })).rejects.toThrow(
        'Draft is not in APPROVED state',
      );
    });
  });
});
