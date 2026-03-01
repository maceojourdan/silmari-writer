/**
 * verifyClaims.feedbackLoop.test.ts - Feedback Loop: Timeout / retry scenarios
 *
 * Additional tests:
 * - Simulate no response (timeout) → retry attempts <= 3
 * - Final state: verification_request.status === 'failed'
 * - Drafting remains disabled
 *
 * Resource: db-h2s4 (service)
 * Path: 321-verify-key-claims-via-voice-or-sms
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';
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
    createSession: vi.fn(),
    createStoryRecord: vi.fn(),
    deleteSession: vi.fn(),
    findAnswerSessionById: vi.fn(),
    findStoryRecordBySessionId: vi.fn(),
    updateSessionAndStoryRecord: vi.fn(),
    saveSlots: vi.fn(),
    updateAnswerSessionState: vi.fn(),
  },
}));

import { VerificationService } from '../VerificationService';
import type { VerificationClient, VerificationTimer, TokenGenerator } from '../VerificationService';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);
const mockRequestDAO = vi.mocked(VerificationRequestDAO);

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const sessionId = 'session-321-feedback';
const testToken = 'vrf-feedback-token';
const allClaimIds = ['claim-m', 'claim-s', 'claim-p', 'claim-sec'];

function createUnverifiedClaims(): ClaimRecord[] {
  return [
    { id: 'claim-m', sessionId, category: 'metrics', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Revenue +40%', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-s', sessionId, category: 'scope', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Team of 12', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-p', sessionId, category: 'production', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: '3 regions', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-sec', sessionId, category: 'security', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'SOC2', verifiedAt: null, createdAt: now, updatedAt: now },
  ];
}

function createPendingRequest(overrides: Partial<VerificationRequest> = {}): VerificationRequest {
  return {
    id: 'req-fb',
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

const instantTimer: VerificationTimer = {
  async delay(): Promise<void> {},
};

const fixedTokenGenerator: TokenGenerator = {
  generate() { return testToken; },
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Verify Claims Feedback Loops — Timeout and Retry Scenarios', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(createUnverifiedClaims());
    mockRequestDAO.create.mockResolvedValue(createPendingRequest());
    mockRequestDAO.logDeliveryAttempt.mockResolvedValue({
      id: 'attempt-fb', requestId: 'req-fb', attemptNumber: 1, status: 'failed', createdAt: now,
    });
  });

  describe('Delivery timeout / no response', () => {
    it('should make exactly 3 delivery attempts before failing', async () => {
      const failClient: VerificationClient = {
        async sendMessage() { throw new Error('Timeout: no response'); },
      };

      mockRequestDAO.updateStatus.mockResolvedValue({
        ...createPendingRequest(),
        status: 'failed',
        attemptCount: 3,
      });

      try {
        await VerificationService.initiateVerification(
          sessionId, failClient, instantTimer, fixedTokenGenerator,
        );
      } catch {
        // expected
      }

      // Verify exactly 3 delivery attempts were logged
      expect(mockRequestDAO.logDeliveryAttempt).toHaveBeenCalledTimes(3);
    });

    it('should mark verification request as failed after 3 timeout attempts', async () => {
      const failClient: VerificationClient = {
        async sendMessage() { throw new Error('Timeout'); },
      };

      mockRequestDAO.updateStatus.mockResolvedValue({
        ...createPendingRequest(),
        status: 'failed',
        attemptCount: 3,
      });

      try {
        await VerificationService.initiateVerification(
          sessionId, failClient, instantTimer, fixedTokenGenerator,
        );
      } catch {
        // expected
      }

      expect(mockRequestDAO.updateStatus).toHaveBeenCalledWith('req-fb', 'failed', 3);
    });

    it('should throw DELIVERY_FAILED error after max retries', async () => {
      const failClient: VerificationClient = {
        async sendMessage() { throw new Error('Timeout'); },
      };

      mockRequestDAO.updateStatus.mockResolvedValue({
        ...createPendingRequest(),
        status: 'failed',
        attemptCount: 3,
      });

      try {
        await VerificationService.initiateVerification(
          sessionId, failClient, instantTimer, fixedTokenGenerator,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('DELIVERY_FAILED');
      }
    });
  });

  describe('Drafting remains disabled after failed verification', () => {
    it('should throw VerificationStateInconsistentError when trying to enable drafting with unverified claims', async () => {
      // Claims remain unverified after failed verification
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(createUnverifiedClaims());

      try {
        await VerificationService.enableDrafting(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('VERIFICATION_STATE_INCONSISTENT');
      }
    });
  });

  describe('Partial confirmation retry flow', () => {
    it('should increment attempt count on partial confirmation', async () => {
      const request = createPendingRequest({ attemptCount: 1 });
      mockRequestDAO.findByToken.mockResolvedValue(request);
      mockRequestDAO.updateStatus.mockResolvedValue({
        ...request,
        status: 'failed',
        attemptCount: 2,
      });

      try {
        await VerificationService.handleInboundConfirmation({
          token: testToken,
          confirmedClaimIds: ['claim-m'], // Only 1 of 4
        });
      } catch {
        // expected
      }

      // Attempt count should be incremented from 1 to 2
      expect(mockRequestDAO.updateStatus).toHaveBeenCalledWith('req-fb', 'failed', 2);
    });

    it('should throw CONFIRMATION_FAILED on the 3rd partial attempt', async () => {
      const request = createPendingRequest({ attemptCount: 2 });
      mockRequestDAO.findByToken.mockResolvedValue(request);
      mockRequestDAO.updateStatus.mockResolvedValue({
        ...request,
        status: 'failed',
        attemptCount: 3,
      });

      try {
        await VerificationService.handleInboundConfirmation({
          token: testToken,
          confirmedClaimIds: ['claim-m'],
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('CONFIRMATION_FAILED');
      }
    });
  });
});
