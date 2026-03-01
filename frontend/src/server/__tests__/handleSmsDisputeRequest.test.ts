/**
 * handleSmsDisputeRequest.test.ts - Unit test for the SMS dispute request handler.
 *
 * Step 2 of Path 322: Invoke dispute handling service.
 *
 * TLA+ properties:
 * - Reachability: Handler calls ClaimDisputeService.handleDispute(claimantId, claimIds).
 * - TypeInvariant: Arguments match expected TypeScript types.
 * - ErrorConsistency: If service throws → returns DisputeErrors.SERVICE_INVOCATION_FAILED.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DisputeError } from '@/server/error_definitions/DisputeErrors';

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

vi.mock('@/server/services/ClaimDisputeService', () => ({
  ClaimDisputeService: {
    handleDispute: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { HandleSmsDisputeRequestHandler } from '@/server/request_handlers/HandleSmsDisputeRequestHandler';
import { ClaimDisputeService } from '@/server/services/ClaimDisputeService';

const mockService = vi.mocked(ClaimDisputeService);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const disputePayload = {
  claimantId: 'claimant-001',
  disputedClaimIds: ['claim-001', 'claim-002'],
};

const serviceResult = {
  updatedClaims: [
    {
      id: 'claim-001',
      sessionId: 'session-001',
      category: 'metrics' as const,
      status: 'not_verified' as const,
      content: 'I increased sales by 40%',
      disputedAt: now,
      createdAt: now,
      updatedAt: now,
    },
    {
      id: 'claim-002',
      sessionId: 'session-001',
      category: 'scope' as const,
      status: 'not_verified' as const,
      content: 'Led a team of 15 engineers',
      disputedAt: now,
      createdAt: now,
      updatedAt: now,
    },
  ],
  caseBlocked: true,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('HandleSmsDisputeRequestHandler — Step 2', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // Reachability
  // =========================================================================

  describe('Reachability', () => {
    it('should call ClaimDisputeService.handleDispute with correct arguments', async () => {
      mockService.handleDispute.mockResolvedValue(serviceResult);

      await HandleSmsDisputeRequestHandler.handle(disputePayload);

      expect(mockService.handleDispute).toHaveBeenCalledWith(
        'claimant-001',
        ['claim-001', 'claim-002'],
      );
    });

    it('should return the service result', async () => {
      mockService.handleDispute.mockResolvedValue(serviceResult);

      const result = await HandleSmsDisputeRequestHandler.handle(disputePayload);

      expect(result).toEqual(serviceResult);
    });
  });

  // =========================================================================
  // TypeInvariant
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should pass claimantId as string and disputedClaimIds as string[]', async () => {
      mockService.handleDispute.mockResolvedValue(serviceResult);

      await HandleSmsDisputeRequestHandler.handle(disputePayload);

      const [claimantId, claimIds] = mockService.handleDispute.mock.calls[0];
      expect(typeof claimantId).toBe('string');
      expect(Array.isArray(claimIds)).toBe(true);
      claimIds.forEach((id) => {
        expect(typeof id).toBe('string');
      });
    });
  });

  // =========================================================================
  // ErrorConsistency
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should throw SERVICE_INVOCATION_FAILED when service throws unknown error', async () => {
      mockService.handleDispute.mockRejectedValue(new Error('Service crashed'));

      try {
        await HandleSmsDisputeRequestHandler.handle(disputePayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('SERVICE_INVOCATION_FAILED');
        expect((e as DisputeError).statusCode).toBe(500);
      }
    });

    it('should rethrow DisputeError as-is (known errors)', async () => {
      const knownError = new DisputeError('Claim not found', 'CLAIM_NOT_FOUND', 404);
      mockService.handleDispute.mockRejectedValue(knownError);

      try {
        await HandleSmsDisputeRequestHandler.handle(disputePayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('CLAIM_NOT_FOUND');
        expect((e as DisputeError).statusCode).toBe(404);
      }
    });
  });
});
