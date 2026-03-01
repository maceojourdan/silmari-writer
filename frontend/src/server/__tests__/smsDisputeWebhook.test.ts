/**
 * smsDisputeWebhook.test.ts - Unit test for the SMS dispute webhook endpoint.
 *
 * Step 1 of Path 322: Receive SMS dispute response.
 *
 * TLA+ properties:
 * - Reachability: POST valid webhook payload → 200 with structured body.
 * - TypeInvariant: Response body matches SmsDisputePayloadSchema.
 * - ErrorConsistency:
 *   - Malformed body → 400 with DisputeErrors.MALFORMED_WEBHOOK.
 *   - Unknown verification request → 404 with DisputeErrors.VERIFICATION_REQUEST_NOT_FOUND.
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { z } from 'zod';
import { DisputeError } from '@/server/error_definitions/DisputeErrors';

// ---------------------------------------------------------------------------
// Mocks: DAO layer (lowest level)
// ---------------------------------------------------------------------------

vi.mock('@/server/data_access_objects/VerificationRequestDAO', () => ({
  VerificationRequestDAO: {
    findByToken: vi.fn(),
    updateStatus: vi.fn(),
    create: vi.fn(),
    findBySessionId: vi.fn(),
    logDeliveryAttempt: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/ClaimCaseDAO', () => ({
  ClaimCaseDAO: {
    getClaimById: vi.fn(),
    updateClaimVerificationStatus: vi.fn(),
    getCaseByClaimantId: vi.fn(),
    updateCaseDraftingStatus: vi.fn(),
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

import {
  SmsDisputePayloadSchema,
  parseSmsDisputeWebhook,
} from '@/server/endpoints/smsDisputeWebhook';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';

const mockVerificationDAO = vi.mocked(VerificationRequestDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const validPayload = {
  token: 'verify-token-abc123',
  claimantId: 'claimant-001',
  disputedClaimIds: ['claim-001', 'claim-002'],
};

const activeVerificationRequest = {
  id: 'vr-001',
  sessionId: 'session-001',
  status: 'pending' as const,
  attemptCount: 1,
  token: 'verify-token-abc123',
  claimIds: ['claim-001', 'claim-002', 'claim-003'],
  contactPhone: '+15551234567',
  contactMethod: 'sms' as const,
  createdAt: now,
  updatedAt: now,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SMS Dispute Webhook — Step 1', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // Reachability
  // =========================================================================

  describe('Reachability', () => {
    it('should accept valid webhook payload and return structured dispute data', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);

      const result = await parseSmsDisputeWebhook(validPayload);

      expect(result).toEqual({
        claimantId: 'claimant-001',
        disputedClaimIds: ['claim-001', 'claim-002'],
      });
    });

    it('should validate token against active verification requests', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);

      await parseSmsDisputeWebhook(validPayload);

      expect(mockVerificationDAO.findByToken).toHaveBeenCalledWith('verify-token-abc123');
    });
  });

  // =========================================================================
  // TypeInvariant
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should validate response matches SmsDisputePayloadSchema', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);

      const result = await parseSmsDisputeWebhook(validPayload);

      const parsed = SmsDisputePayloadSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return correct types for claimantId and disputedClaimIds', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);

      const result = await parseSmsDisputeWebhook(validPayload);

      expect(typeof result.claimantId).toBe('string');
      expect(Array.isArray(result.disputedClaimIds)).toBe(true);
      result.disputedClaimIds.forEach((id) => {
        expect(typeof id).toBe('string');
      });
    });
  });

  // =========================================================================
  // ErrorConsistency
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should throw MALFORMED_WEBHOOK for missing token', async () => {
      try {
        await parseSmsDisputeWebhook({ claimantId: 'c-1', disputedClaimIds: ['id'] });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('MALFORMED_WEBHOOK');
        expect((e as DisputeError).statusCode).toBe(400);
      }
    });

    it('should throw MALFORMED_WEBHOOK for missing claimantId', async () => {
      try {
        await parseSmsDisputeWebhook({ token: 'abc', disputedClaimIds: ['id'] });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('MALFORMED_WEBHOOK');
      }
    });

    it('should throw MALFORMED_WEBHOOK for empty disputedClaimIds', async () => {
      try {
        await parseSmsDisputeWebhook({ token: 'abc', claimantId: 'c-1', disputedClaimIds: [] });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('MALFORMED_WEBHOOK');
      }
    });

    it('should throw MALFORMED_WEBHOOK for non-object payload', async () => {
      try {
        await parseSmsDisputeWebhook('not an object');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('MALFORMED_WEBHOOK');
      }
    });

    it('should throw VERIFICATION_REQUEST_NOT_FOUND for unknown token', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(null);

      try {
        await parseSmsDisputeWebhook(validPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('VERIFICATION_REQUEST_NOT_FOUND');
        expect((e as DisputeError).statusCode).toBe(404);
      }
    });
  });
});
