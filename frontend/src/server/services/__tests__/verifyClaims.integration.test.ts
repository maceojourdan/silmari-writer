/**
 * verifyClaims.integration.test.ts - Terminal Condition: Full path integration test
 *
 * Exercises the complete verification path:
 * 1. Seed unverified claims (all categories present)
 * 2. Detect eligibility
 * 3. Initiate verification (mock SMS success)
 * 4. Simulate full confirmation
 * 5. Mark claims verified
 * 6. Enable drafting
 *
 * Asserts:
 * - All claims status === 'verified'
 * - Drafting enabled flag true
 * - Verification request status === 'confirmed'
 *
 * Resource: db-h2s4 (service)
 * Path: 321-verify-key-claims-via-voice-or-sms
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';
import type { Session } from '@/server/data_structures/Session';

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
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);
const mockRequestDAO = vi.mocked(VerificationRequestDAO);
const mockSessionDAO = vi.mocked(SessionDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const sessionId = 'session-321-integration';
const testToken = 'vrf-integration-token';

const allClaimIds = ['claim-m', 'claim-s', 'claim-p', 'claim-sec'];

function createUnverifiedClaims(): ClaimRecord[] {
  return [
    { id: 'claim-m', sessionId, category: 'metrics', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Revenue +40%', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-s', sessionId, category: 'scope', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Team of 12', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-p', sessionId, category: 'production', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: '3 regions', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-sec', sessionId, category: 'security', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'SOC2', verifiedAt: null, createdAt: now, updatedAt: now },
  ];
}

function createVerifiedClaims(): ClaimRecord[] {
  const verifiedAt = new Date().toISOString();
  return createUnverifiedClaims().map(c => ({
    ...c,
    status: 'verified' as const,
    verifiedAt,
    updatedAt: verifiedAt,
  }));
}

function createPendingRequest(): VerificationRequest {
  return {
    id: 'req-int',
    sessionId,
    status: 'pending',
    attemptCount: 0,
    token: testToken,
    claimIds: allClaimIds,
    contactPhone: '+15551234567',
    contactMethod: 'sms',
    createdAt: now,
    updatedAt: now,
  };
}

function createDraftEnabledSession(): Session {
  return {
    id: sessionId,
    state: 'DRAFT_ENABLED',
    requiredInputsComplete: true,
    createdAt: now,
    updatedAt: now,
  };
}

const instantTimer: VerificationTimer = {
  async delay(): Promise<void> {},
};

const fixedTokenGenerator: TokenGenerator = {
  generate() { return testToken; },
};

const successClient: VerificationClient = {
  async sendMessage() { return { sid: 'SM-integration' }; },
};

// ---------------------------------------------------------------------------
// Integration Test
// ---------------------------------------------------------------------------

describe('Verify Claims Integration — Full Path End-to-End', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should complete the full verification path: eligibility → initiate → confirm → mark verified → enable drafting', async () => {
    // -----------------------------------------------------------------------
    // Step 1: Seed unverified claims - Detect eligibility
    // -----------------------------------------------------------------------

    mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(createUnverifiedClaims());

    const eligibilityResult = await VerificationService.detectEligibility(sessionId);

    expect(eligibilityResult.eligible).toBe(true);
    expect(eligibilityResult.claims).toHaveLength(4);

    // -----------------------------------------------------------------------
    // Step 2: Initiate verification (mock SMS success)
    // -----------------------------------------------------------------------

    mockRequestDAO.create.mockResolvedValue(createPendingRequest());
    mockRequestDAO.logDeliveryAttempt.mockResolvedValue({
      id: 'attempt-1',
      requestId: 'req-int',
      attemptNumber: 1,
      status: 'success',
      externalId: 'SM-integration',
      createdAt: now,
    });

    const request = await VerificationService.initiateVerification(
      sessionId, successClient, instantTimer, fixedTokenGenerator,
    );

    expect(request.status).toBe('pending');
    expect(request.token).toBe(testToken);

    // -----------------------------------------------------------------------
    // Step 3: Simulate full confirmation
    // -----------------------------------------------------------------------

    mockRequestDAO.findByToken.mockResolvedValue(createPendingRequest());
    mockRequestDAO.updateStatus.mockResolvedValue({
      ...createPendingRequest(),
      status: 'confirmed',
    });

    const confirmResult = await VerificationService.handleInboundConfirmation({
      token: testToken,
      confirmedClaimIds: allClaimIds,
    });

    expect(confirmResult.fullConfirmation).toBe(true);

    // Assert verification request was updated to confirmed
    expect(mockRequestDAO.updateStatus).toHaveBeenCalledWith('req-int', 'confirmed', 0);

    // -----------------------------------------------------------------------
    // Step 4: Mark claims verified
    // -----------------------------------------------------------------------

    // After confirmation, get unverified claims to mark them
    mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(createUnverifiedClaims());
    mockClaimDAO.updateStatusToVerified.mockResolvedValue(createVerifiedClaims());

    const verifiedClaims = await VerificationService.markClaimsVerified(sessionId);

    // Assert all claims status === 'verified'
    for (const claim of verifiedClaims) {
      expect(claim.status).toBe('verified');
    }

    // -----------------------------------------------------------------------
    // Step 5: Enable drafting
    // -----------------------------------------------------------------------

    // Now no unverified claims remain
    mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([]);
    mockSessionDAO.updateState.mockResolvedValue(createDraftEnabledSession());

    const session = await VerificationService.enableDrafting(sessionId);

    // Assert drafting enabled
    expect(session.state).toBe('DRAFT_ENABLED');
  });

  it('should prove end-to-end Reachability: all terminal conditions met', async () => {
    // Setup full mock chain
    mockClaimDAO.getUnverifiedClaimsBySession
      .mockResolvedValueOnce(createUnverifiedClaims()) // Step 1 eligibility
      .mockResolvedValueOnce(createUnverifiedClaims()) // Step 2 initiate (calls eligibility)
      .mockResolvedValueOnce(createUnverifiedClaims()) // Step 4 markVerified
      .mockResolvedValueOnce([]); // Step 5 enableDrafting (none unverified)

    mockRequestDAO.create.mockResolvedValue(createPendingRequest());
    mockRequestDAO.logDeliveryAttempt.mockResolvedValue({
      id: 'a-1', requestId: 'req-int', attemptNumber: 1, status: 'success', createdAt: now,
    });
    mockRequestDAO.findByToken.mockResolvedValue(createPendingRequest());
    mockRequestDAO.updateStatus.mockResolvedValue({ ...createPendingRequest(), status: 'confirmed' });
    mockClaimDAO.updateStatusToVerified.mockResolvedValue(createVerifiedClaims());
    mockSessionDAO.updateState.mockResolvedValue(createDraftEnabledSession());

    // Execute full path
    const elig = await VerificationService.detectEligibility(sessionId);
    const req = await VerificationService.initiateVerification(sessionId, successClient, instantTimer, fixedTokenGenerator);
    const conf = await VerificationService.handleInboundConfirmation({ token: testToken, confirmedClaimIds: allClaimIds });
    const verified = await VerificationService.markClaimsVerified(sessionId);
    const session = await VerificationService.enableDrafting(sessionId);

    // Terminal conditions
    expect(elig.eligible).toBe(true);
    expect(req.status).toBe('pending');
    expect(conf.fullConfirmation).toBe(true);
    for (const c of verified) expect(c.status).toBe('verified');
    expect(session.state).toBe('DRAFT_ENABLED');
  });
});
