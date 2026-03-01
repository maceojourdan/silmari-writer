/**
 * step2.initiateVerification.test.ts - Step 2: Initiate voice or SMS verification request
 *
 * TLA+ Properties:
 * - Reachability: Mock Twilio success → verification_request.status === 'pending', delivery_attempt logged
 * - TypeInvariant: Returned object matches VerificationRequest type, attemptCount is number
 * - ErrorConsistency: Mock Twilio failure × 3 → status === 'failed', DeliveryFailed error
 *
 * Resource: db-h2s4 (service)
 * Path: 321-verify-key-claims-via-voice-or-sms
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import { VerificationRequestSchema } from '@/server/data_structures/VerificationRequest';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';

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
import type { VerificationClient, VerificationTimer, TokenGenerator } from '../VerificationService';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);
const mockRequestDAO = vi.mocked(VerificationRequestDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const sessionId = 'session-321-step2';
const testToken = 'vrf-test-token-12345';

function createAllCategoryClaims(): ClaimRecord[] {
  return [
    { id: 'claim-m', sessionId, category: 'metrics', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Revenue +40%', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-s', sessionId, category: 'scope', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Team of 12', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-p', sessionId, category: 'production', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: '3 regions', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-sec', sessionId, category: 'security', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'SOC2', verifiedAt: null, createdAt: now, updatedAt: now },
  ];
}

function createPendingRequest(): VerificationRequest {
  return {
    id: 'req-001',
    sessionId,
    status: 'pending',
    attemptCount: 0,
    token: testToken,
    claimIds: ['claim-m', 'claim-s', 'claim-p', 'claim-sec'],
    contactPhone: '+15551234567',
    contactMethod: 'sms',
    createdAt: now,
    updatedAt: now,
  };
}

const instantTimer: VerificationTimer = {
  async delay(): Promise<void> { /* no delay */ },
};

const fixedTokenGenerator: TokenGenerator = {
  generate() { return testToken; },
};

function createMockClient(responses: Array<{ sid: string } | Error>): VerificationClient {
  let callCount = 0;
  return {
    async sendMessage(): Promise<{ sid: string }> {
      const response = responses[callCount++];
      if (response instanceof Error) throw response;
      return response;
    },
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.initiateVerification — Step 2: Initiate verification request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    // Default: all categories present
    mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(createAllCategoryClaims());
    // Default: create returns pending request
    mockRequestDAO.create.mockResolvedValue(createPendingRequest());
    // Default: log delivery resolves
    mockRequestDAO.logDeliveryAttempt.mockResolvedValue({
      id: 'attempt-1',
      requestId: 'req-001',
      attemptNumber: 1,
      status: 'success',
      createdAt: now,
    });
    mockRequestDAO.updateStatus.mockResolvedValue({
      ...createPendingRequest(),
      status: 'failed',
      attemptCount: 3,
    });
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return verification request with pending status on successful delivery', async () => {
      const client = createMockClient([{ sid: 'SM-abc123' }]);

      const result = await VerificationService.initiateVerification(
        sessionId, client, instantTimer, fixedTokenGenerator,
      );

      expect(result.status).toBe('pending');
    });

    it('should log a successful delivery attempt', async () => {
      const client = createMockClient([{ sid: 'SM-abc123' }]);

      await VerificationService.initiateVerification(
        sessionId, client, instantTimer, fixedTokenGenerator,
      );

      expect(mockRequestDAO.logDeliveryAttempt).toHaveBeenCalledWith(
        expect.objectContaining({
          requestId: 'req-001',
          attemptNumber: 1,
          status: 'success',
          externalId: 'SM-abc123',
        }),
      );
    });

    it('should create a verification request record in the DAO', async () => {
      const client = createMockClient([{ sid: 'SM-abc123' }]);

      await VerificationService.initiateVerification(
        sessionId, client, instantTimer, fixedTokenGenerator,
      );

      expect(mockRequestDAO.create).toHaveBeenCalledWith(
        expect.objectContaining({
          sessionId,
          contactPhone: '+15551234567',
          contactMethod: 'sms',
          token: testToken,
        }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object matching VerificationRequest schema', async () => {
      const client = createMockClient([{ sid: 'SM-type' }]);

      const result = await VerificationService.initiateVerification(
        sessionId, client, instantTimer, fixedTokenGenerator,
      );

      const parsed = VerificationRequestSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have attemptCount as a number', async () => {
      const client = createMockClient([{ sid: 'SM-type' }]);

      const result = await VerificationService.initiateVerification(
        sessionId, client, instantTimer, fixedTokenGenerator,
      );

      expect(typeof result.attemptCount).toBe('number');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw DeliveryFailed after 3 consecutive failures', async () => {
      const client = createMockClient([
        new Error('Fail 1'),
        new Error('Fail 2'),
        new Error('Fail 3'),
      ]);

      try {
        await VerificationService.initiateVerification(
          sessionId, client, instantTimer, fixedTokenGenerator,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('DELIVERY_FAILED');
      }
    });

    it('should mark request as failed after exhausting retries', async () => {
      const client = createMockClient([
        new Error('Fail 1'),
        new Error('Fail 2'),
        new Error('Fail 3'),
      ]);

      try {
        await VerificationService.initiateVerification(
          sessionId, client, instantTimer, fixedTokenGenerator,
        );
      } catch {
        // expected
      }

      expect(mockRequestDAO.updateStatus).toHaveBeenCalledWith('req-001', 'failed', 3);
    });

    it('should log all 3 failed delivery attempts', async () => {
      const client = createMockClient([
        new Error('Fail 1'),
        new Error('Fail 2'),
        new Error('Fail 3'),
      ]);

      try {
        await VerificationService.initiateVerification(
          sessionId, client, instantTimer, fixedTokenGenerator,
        );
      } catch {
        // expected
      }

      expect(mockRequestDAO.logDeliveryAttempt).toHaveBeenCalledTimes(3);
      expect(mockRequestDAO.logDeliveryAttempt).toHaveBeenCalledWith(
        expect.objectContaining({ attemptNumber: 1, status: 'failed' }),
      );
      expect(mockRequestDAO.logDeliveryAttempt).toHaveBeenCalledWith(
        expect.objectContaining({ attemptNumber: 3, status: 'failed' }),
      );
    });

    it('should succeed after 2 failures followed by success', async () => {
      const client = createMockClient([
        new Error('Fail 1'),
        new Error('Fail 2'),
        { sid: 'SM-recovered' },
      ]);

      const result = await VerificationService.initiateVerification(
        sessionId, client, instantTimer, fixedTokenGenerator,
      );

      expect(result.status).toBe('pending');
    });

    it('should throw INVALID_CONTACT when no phone number found', async () => {
      // Claims without phone numbers
      const claimsNoPhone: ClaimRecord[] = [
        { id: 'claim-m', sessionId, category: 'metrics', status: 'unverified', content: 'Revenue +40%', verifiedAt: null, createdAt: now, updatedAt: now },
        { id: 'claim-s', sessionId, category: 'scope', status: 'unverified', content: 'Team', verifiedAt: null, createdAt: now, updatedAt: now },
        { id: 'claim-p', sessionId, category: 'production', status: 'unverified', content: '3 regions', verifiedAt: null, createdAt: now, updatedAt: now },
        { id: 'claim-sec', sessionId, category: 'security', status: 'unverified', content: 'SOC2', verifiedAt: null, createdAt: now, updatedAt: now },
      ];
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(claimsNoPhone);
      const client = createMockClient([{ sid: 'SM-nope' }]);

      try {
        await VerificationService.initiateVerification(
          sessionId, client, instantTimer, fixedTokenGenerator,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('INVALID_CONTACT');
      }
    });
  });
});
