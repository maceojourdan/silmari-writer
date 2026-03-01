/**
 * confirmTruthCheck API Contract Tests
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Properties tested:
 * - Reachability: mock fetch success (200) → correct POST to /api/truth-checks/confirm
 * - TypeInvariant: request body matches ConfirmTruthCheckRequest; response matches schema
 * - ErrorConsistency: mock network failure → retries up to 2 times → final failure returned
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  confirmTruthCheck,
  ConfirmTruthCheckResponseSchema,
  type ConfirmTruthCheckRequest,
} from '@/api_contracts/confirmTruthCheck';

const mockFetch = vi.fn();

describe('confirmTruthCheck API Contract', () => {
  const validPayload: ConfirmTruthCheckRequest = {
    claim_id: 'claim-001',
    status: 'confirmed',
    source: 'Annual Revenue Report 2025',
  };

  const successResponse = {
    id: 'tc-001',
    claim_id: 'claim-001',
    status: 'confirmed',
    source: 'Annual Revenue Report 2025',
    created_at: '2026-02-28T12:00:00.000Z',
  };

  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  describe('Reachability: POST to /api/truth-checks/confirm', () => {
    it('should POST to the correct endpoint', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      await confirmTruthCheck(validPayload);

      expect(mockFetch).toHaveBeenCalledTimes(1);
      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe('/api/truth-checks/confirm');
      expect(options.method).toBe('POST');
    });

    it('should send correct JSON body', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      await confirmTruthCheck(validPayload);

      const [, options] = mockFetch.mock.calls[0];
      expect(JSON.parse(options.body)).toEqual({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
      });
    });

    it('should return parsed response on success', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      const result = await confirmTruthCheck(validPayload);

      expect(result.id).toBe('tc-001');
      expect(result.claim_id).toBe('claim-001');
      expect(result.status).toBe('confirmed');
    });
  });

  describe('TypeInvariant: request and response types', () => {
    it('should match ConfirmTruthCheckRequest type', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => successResponse,
      });

      await confirmTruthCheck(validPayload);

      const [, options] = mockFetch.mock.calls[0];
      const body = JSON.parse(options.body);
      expect(body).toHaveProperty('claim_id');
      expect(body).toHaveProperty('status');
      expect(body).toHaveProperty('source');
      expect(['confirmed', 'denied']).toContain(body.status);
    });

    it('should validate response against Zod schema', () => {
      const parsed = ConfirmTruthCheckResponseSchema.safeParse(successResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject invalid response shape', () => {
      const invalid = { garbage: true };
      const parsed = ConfirmTruthCheckResponseSchema.safeParse(invalid);
      expect(parsed.success).toBe(false);
    });
  });

  describe('ErrorConsistency: retry logic and failure', () => {
    it('should retry up to 2 times on network failure (3 attempts total)', async () => {
      mockFetch
        .mockRejectedValueOnce(new TypeError('Failed to fetch'))
        .mockRejectedValueOnce(new TypeError('Failed to fetch'))
        .mockRejectedValueOnce(new TypeError('Failed to fetch'));

      await expect(confirmTruthCheck(validPayload)).rejects.toThrow();

      expect(mockFetch).toHaveBeenCalledTimes(3);
    });

    it('should succeed on retry after initial failure', async () => {
      mockFetch
        .mockRejectedValueOnce(new TypeError('Failed to fetch'))
        .mockResolvedValueOnce({
          ok: true,
          json: async () => successResponse,
        });

      const result = await confirmTruthCheck(validPayload);

      expect(result.claim_id).toBe('claim-001');
      expect(mockFetch).toHaveBeenCalledTimes(2);
    });

    it('should not retry on 4xx client errors', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 400,
        json: async () => ({ code: 'TRUTH_CHECK_VALIDATION_ERROR', message: 'Invalid claim_id' }),
      });

      await expect(confirmTruthCheck(validPayload)).rejects.toThrow('Invalid claim_id');
      expect(mockFetch).toHaveBeenCalledTimes(1);
    });

    it('should retry on 5xx server errors', async () => {
      mockFetch
        .mockResolvedValueOnce({
          ok: false,
          status: 500,
          json: async () => ({ code: 'INTERNAL_ERROR', message: 'DB down' }),
        })
        .mockResolvedValueOnce({
          ok: true,
          json: async () => successResponse,
        });

      const result = await confirmTruthCheck(validPayload);

      expect(result.claim_id).toBe('claim-001');
      expect(mockFetch).toHaveBeenCalledTimes(2);
    });

    it('should throw on malformed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      await expect(confirmTruthCheck(validPayload)).rejects.toThrow(/Invalid response/);
    });
  });
});
