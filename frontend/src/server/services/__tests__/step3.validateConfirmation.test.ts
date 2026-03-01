/**
 * step3.validateConfirmation.test.ts - Step 3: Receive and validate claimant confirmation
 *
 * TLA+ Properties:
 * - Reachability: Pending request + all claim IDs confirmed → fullConfirmation === true
 * - TypeInvariant: Result type matches ConfirmationResult
 * - ErrorConsistency: Partial confirmation → request failed, retry if < 3 attempts
 *
 * Resource: db-h2s4 (service)
 * Path: 321-verify-key-claims-via-voice-or-sms
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import { ConfirmationResultSchema } from '@/server/data_structures/VerificationRequest';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';

// Mock the verification logger
vi.mock('@/server/logging/verificationLogger', () => ({
  verificationLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock the ClaimDAO
vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getUnverifiedClaimsBySession: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    updateStatusToVerified: vi.fn(),
  },
}));

// Mock the VerificationRequestDAO
vi.mock('@/server/data_access_objects/VerificationRequestDAO', () => ({
  VerificationRequestDAO: {
    create: vi.fn(),
    findByToken: vi.fn(),
    findBySessionId: vi.fn(),
    updateStatus: vi.fn(),
    logDeliveryAttempt: vi.fn(),
  },
}));

// Mock the SessionDAO
vi.mock('@/server/data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
  },
}));

import { VerificationService } from '../VerificationService';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';

const mockRequestDAO = vi.mocked(VerificationRequestDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const sessionId = 'session-321-step3';
const testToken = 'vrf-confirmation-token';

const allClaimIds = ['claim-m', 'claim-s', 'claim-p', 'claim-sec'];

function createPendingRequest(overrides: Partial<VerificationRequest> = {}): VerificationRequest {
  return {
    id: 'req-003',
    sessionId,
    status: 'pending',
    attemptCount: 0,
    token: testToken,
    claimIds: allClaimIds,
    contactPhone: '+15551234567',
    contactMethod: 'sms',
    createdAt: now,
    updatedAt: now,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.handleInboundConfirmation — Step 3: Validate claimant confirmation', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    // Default: findByToken returns pending request
    mockRequestDAO.findByToken.mockResolvedValue(createPendingRequest());
    // Default: updateStatus resolves
    mockRequestDAO.updateStatus.mockResolvedValue({
      ...createPendingRequest(),
      status: 'confirmed',
    });
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return fullConfirmation === true when all claim IDs are confirmed', async () => {
      const result = await VerificationService.handleInboundConfirmation({
        token: testToken,
        confirmedClaimIds: allClaimIds,
      });

      expect(result.fullConfirmation).toBe(true);
    });

    it('should include all confirmed claim IDs in the result', async () => {
      const result = await VerificationService.handleInboundConfirmation({
        token: testToken,
        confirmedClaimIds: allClaimIds,
      });

      expect(result.confirmedClaimIds).toEqual(allClaimIds);
    });

    it('should update request status to confirmed', async () => {
      await VerificationService.handleInboundConfirmation({
        token: testToken,
        confirmedClaimIds: allClaimIds,
      });

      expect(mockRequestDAO.updateStatus).toHaveBeenCalledWith('req-003', 'confirmed', 0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching ConfirmationResult schema', async () => {
      const result = await VerificationService.handleInboundConfirmation({
        token: testToken,
        confirmedClaimIds: allClaimIds,
      });

      const parsed = ConfirmationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have fullConfirmation as boolean', async () => {
      const result = await VerificationService.handleInboundConfirmation({
        token: testToken,
        confirmedClaimIds: allClaimIds,
      });

      expect(typeof result.fullConfirmation).toBe('boolean');
    });

    it('should have requestId as string', async () => {
      const result = await VerificationService.handleInboundConfirmation({
        token: testToken,
        confirmedClaimIds: allClaimIds,
      });

      expect(typeof result.requestId).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw CONFIRMATION_FAILED on partial confirmation', async () => {
      // Only 2 of 4 claim IDs confirmed
      try {
        await VerificationService.handleInboundConfirmation({
          token: testToken,
          confirmedClaimIds: ['claim-m', 'claim-s'],
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('CONFIRMATION_FAILED');
      }
    });

    it('should update request to failed on partial confirmation', async () => {
      mockRequestDAO.updateStatus.mockResolvedValue({
        ...createPendingRequest(),
        status: 'failed',
        attemptCount: 1,
      });

      try {
        await VerificationService.handleInboundConfirmation({
          token: testToken,
          confirmedClaimIds: ['claim-m'],
        });
      } catch {
        // expected
      }

      expect(mockRequestDAO.updateStatus).toHaveBeenCalledWith('req-003', 'failed', 1);
    });

    it('should throw CONFIRMATION_FAILED when no pending request found for token', async () => {
      mockRequestDAO.findByToken.mockResolvedValue(null);

      try {
        await VerificationService.handleInboundConfirmation({
          token: 'bad-token',
          confirmedClaimIds: allClaimIds,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('CONFIRMATION_FAILED');
      }
    });

    it('should include missing claim IDs in error message', async () => {
      mockRequestDAO.updateStatus.mockResolvedValue({
        ...createPendingRequest(),
        status: 'failed',
        attemptCount: 1,
      });

      try {
        await VerificationService.handleInboundConfirmation({
          token: testToken,
          confirmedClaimIds: ['claim-m', 'claim-s'],
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as VerificationError).message).toContain('claim-p');
        expect((e as VerificationError).message).toContain('claim-sec');
      }
    });
  });
});
