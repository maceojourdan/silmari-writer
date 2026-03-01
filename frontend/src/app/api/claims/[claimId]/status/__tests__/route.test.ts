/**
 * Step 4 Tests: Expose updated status to frontend
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * TLA+ Properties tested:
 * - Reachability: GET returns 200 with correct statuses
 * - TypeInvariant: response validates via ClaimStatusResponseSchema
 * - ErrorConsistency: handler throw → 500 with DomainErrors code; logger called
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimStatusResponseSchema } from '@/server/data_structures/DraftingWorkflow';

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

vi.mock('@/server/request_handlers/GetClaimStatusHandler', () => ({
  GetClaimStatusHandler: {
    handle: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { GetClaimStatusHandler } from '@/server/request_handlers/GetClaimStatusHandler';
import { logger } from '@/server/logging/logger';
import { DomainError } from '@/server/error_definitions/DomainErrors';

const mockHandle = vi.mocked(GetClaimStatusHandler.handle);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Import the route handler (must come after mocks)
// ---------------------------------------------------------------------------

import { GET } from '@/app/api/claims/[claimId]/status/route';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeRequest(): Request {
  return new Request('http://localhost/api/claims/claim-001/status', {
    method: 'GET',
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('GET /api/claims/[claimId]/status', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -----------------------------------------------------------------------
  // Reachability
  // -----------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with Unverified claim and On Hold drafting', async () => {
      mockHandle.mockResolvedValue({
        claimStatus: 'UNVERIFIED',
        draftingStatus: 'On Hold',
        timedOut: true,
      });

      const response = await GET(
        makeRequest(),
        { params: Promise.resolve({ claimId: 'claim-001' }) },
      );

      expect(response.status).toBe(200);

      const json = await response.json();
      expect(json).toEqual({
        claimStatus: 'UNVERIFIED',
        draftingStatus: 'On Hold',
        timedOut: true,
      });
    });
  });

  // -----------------------------------------------------------------------
  // TypeInvariant
  // -----------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate response via ClaimStatusResponseSchema', async () => {
      mockHandle.mockResolvedValue({
        claimStatus: 'UNVERIFIED',
        draftingStatus: 'On Hold',
        timedOut: true,
      });

      const response = await GET(
        makeRequest(),
        { params: Promise.resolve({ claimId: 'claim-001' }) },
      );

      const json = await response.json();
      const validation = ClaimStatusResponseSchema.safeParse(json);

      expect(validation.success).toBe(true);
    });
  });

  // -----------------------------------------------------------------------
  // ErrorConsistency
  // -----------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return error status when handler throws DomainError', async () => {
      const domainError = new DomainError(
        'Claim not found',
        'DOMAIN_INTEGRITY_ERROR',
        404,
        false,
      );
      mockHandle.mockRejectedValue(domainError);

      const response = await GET(
        makeRequest(),
        { params: Promise.resolve({ claimId: 'claim-001' }) },
      );

      expect(response.status).toBe(404);

      const json = await response.json();
      expect(json.code).toBe('DOMAIN_INTEGRITY_ERROR');
    });

    it('should return 500 and log when handler throws unknown error', async () => {
      mockHandle.mockRejectedValue(new Error('DB connection failed'));

      const response = await GET(
        makeRequest(),
        { params: Promise.resolve({ claimId: 'claim-001' }) },
      );

      expect(response.status).toBe(500);

      const json = await response.json();
      expect(json.code).toBe('CLAIM_STATUS_LOAD_ERROR');

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should return 400 when claimId is empty', async () => {
      const response = await GET(
        makeRequest(),
        { params: Promise.resolve({ claimId: '' }) },
      );

      expect(response.status).toBe(400);

      const json = await response.json();
      expect(json.code).toBe('VALIDATION_ERROR');
    });
  });
});
