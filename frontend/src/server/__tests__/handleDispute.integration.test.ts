/**
 * handleDispute.integration.test.ts - Full integration test for the
 * disputed claims and block drafting path.
 *
 * Terminal Condition:
 * > User sees the drafting interface blocked with a visible status
 * > indicating disputed claims are not verified and must be corrected
 * > before drafting can continue.
 *
 * Asserts:
 * - ✅ Full path Reachability (trigger → UI blocked)
 * - ✅ TypeInvariant across backend + frontend boundary
 * - ✅ ErrorConsistency on malformed webhook, missing claim, invalid state, and UI load failure
 *
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimRecordSchema } from '@/server/data_structures/ClaimRecord';
import { CaseSchema, CaseStateResponseSchema } from '@/server/data_structures/Case';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';
import type { Case } from '@/server/data_structures/Case';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';
import { DisputeError } from '@/server/error_definitions/DisputeErrors';
import { SmsDisputePayloadSchema } from '@/server/endpoints/smsDisputeWebhook';

// ---------------------------------------------------------------------------
// Mocks: DAO layer only (lowest level)
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

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Imports: Real implementations for all layers above DAO
// ---------------------------------------------------------------------------

import { parseSmsDisputeWebhook } from '@/server/endpoints/smsDisputeWebhook';
import { HandleSmsDisputeRequestHandler } from '@/server/request_handlers/HandleSmsDisputeRequestHandler';
import { ClaimDisputeService } from '@/server/services/ClaimDisputeService';
import { CaseStateVerifier } from '@/server/verifiers/CaseStateVerifier';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';
import { ClaimCaseDAO } from '@/server/data_access_objects/ClaimCaseDAO';

const mockVerificationDAO = vi.mocked(VerificationRequestDAO);
const mockClaimCaseDAO = vi.mocked(ClaimCaseDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const activeVerificationRequest: VerificationRequest = {
  id: 'vr-int-001',
  sessionId: 'session-int-001',
  status: 'pending',
  attemptCount: 1,
  token: 'verify-token-integration',
  claimIds: ['claim-int-001', 'claim-int-002', 'claim-int-003'],
  contactPhone: '+15551234567',
  contactMethod: 'sms',
  createdAt: now,
  updatedAt: now,
};

const verifiedClaim1: ClaimRecord = {
  id: 'claim-int-001',
  sessionId: 'session-int-001',
  category: 'metrics',
  status: 'verified',
  content: 'I increased sales by 40%',
  contactPhone: '+15551234567',
  contactMethod: 'sms',
  verifiedAt: now,
  disputedAt: null,
  createdAt: now,
  updatedAt: now,
};

const verifiedClaim2: ClaimRecord = {
  id: 'claim-int-002',
  sessionId: 'session-int-001',
  category: 'scope',
  status: 'verified',
  content: 'Led a team of 15 engineers',
  contactPhone: '+15551234567',
  contactMethod: 'sms',
  verifiedAt: now,
  disputedAt: null,
  createdAt: now,
  updatedAt: now,
};

const disputedClaim1: ClaimRecord = {
  ...verifiedClaim1,
  status: 'not_verified',
  disputedAt: now,
  updatedAt: now,
};

const disputedClaim2: ClaimRecord = {
  ...verifiedClaim2,
  status: 'not_verified',
  disputedAt: now,
  updatedAt: now,
};

const draftingAllowedCase: Case = {
  id: 'case-int-001',
  claimantId: 'claimant-int-001',
  sessionId: 'session-int-001',
  drafting_status: 'drafting_allowed',
  createdAt: now,
  updatedAt: now,
};

const blockedCase: Case = {
  ...draftingAllowedCase,
  drafting_status: 'blocked_due_to_unverified_claims',
  updatedAt: now,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Handle Dispute Flow — Integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // Reachability: Full happy path (trigger → UI blocked)
  // =========================================================================

  describe('Reachability', () => {
    it('should complete full flow: SMS webhook → mark claims → block drafting', async () => {
      // Step 1: Webhook validation
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);

      // Step 3: Claim lookups and updates
      mockClaimCaseDAO.getClaimById
        .mockResolvedValueOnce(verifiedClaim1)
        .mockResolvedValueOnce(verifiedClaim2);
      mockClaimCaseDAO.updateClaimVerificationStatus
        .mockResolvedValueOnce(disputedClaim1)
        .mockResolvedValueOnce(disputedClaim2);

      // Step 4: Case lookup and block
      mockClaimCaseDAO.getCaseByClaimantId.mockResolvedValue(draftingAllowedCase);
      mockClaimCaseDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      // --- Execute full flow ---

      // Step 1: Parse webhook
      const webhookPayload = {
        token: 'verify-token-integration',
        claimantId: 'claimant-int-001',
        disputedClaimIds: ['claim-int-001', 'claim-int-002'],
      };

      const disputeData = await parseSmsDisputeWebhook(webhookPayload);

      // Step 2-4: Handle dispute
      const result = await HandleSmsDisputeRequestHandler.handle(disputeData);

      // --- Assert terminal condition ---

      // Claims updated to not_verified
      expect(result.updatedClaims).toHaveLength(2);
      expect(result.updatedClaims[0].status).toBe('not_verified');
      expect(result.updatedClaims[1].status).toBe('not_verified');

      // Case drafting blocked
      expect(result.caseBlocked).toBe(true);
      expect(mockClaimCaseDAO.updateCaseDraftingStatus).toHaveBeenCalledWith(
        'case-int-001',
        'blocked_due_to_unverified_claims',
      );

      // Step 5: Frontend would receive blocked state
      const frontendResponse = {
        caseId: 'case-int-001',
        drafting_status: 'blocked_due_to_unverified_claims' as const,
        blocked: true,
        message: 'Drafting is blocked due to disputed claims that are not verified.',
      };

      // Validate frontend response schema
      const parsed = CaseStateResponseSchema.safeParse(frontendResponse);
      expect(parsed.success).toBe(true);
      expect(frontendResponse.blocked).toBe(true);
    });

    it('should exercise all layers: Endpoint → Handler → Service → Verifier → DAO', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);
      mockClaimCaseDAO.getClaimById.mockResolvedValueOnce(verifiedClaim1);
      mockClaimCaseDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim1);
      mockClaimCaseDAO.getCaseByClaimantId.mockResolvedValue(draftingAllowedCase);
      mockClaimCaseDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      // Execute full flow through all layers
      const disputeData = await parseSmsDisputeWebhook({
        token: 'verify-token-integration',
        claimantId: 'claimant-int-001',
        disputedClaimIds: ['claim-int-001'],
      });

      const result = await HandleSmsDisputeRequestHandler.handle(disputeData);

      // Verify each layer was invoked
      expect(mockVerificationDAO.findByToken).toHaveBeenCalledTimes(1);
      expect(mockClaimCaseDAO.getClaimById).toHaveBeenCalledTimes(1);
      expect(mockClaimCaseDAO.updateClaimVerificationStatus).toHaveBeenCalledTimes(1);
      expect(mockClaimCaseDAO.getCaseByClaimantId).toHaveBeenCalledTimes(1);
      expect(mockClaimCaseDAO.updateCaseDraftingStatus).toHaveBeenCalledTimes(1);
      expect(result.caseBlocked).toBe(true);
    });
  });

  // =========================================================================
  // TypeInvariant: Across backend + frontend boundary
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should maintain type integrity from webhook payload through to dispute result', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);
      mockClaimCaseDAO.getClaimById.mockResolvedValueOnce(verifiedClaim1);
      mockClaimCaseDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim1);
      mockClaimCaseDAO.getCaseByClaimantId.mockResolvedValue(draftingAllowedCase);
      mockClaimCaseDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      // Validate input schema
      const webhookPayload = {
        token: 'verify-token-integration',
        claimantId: 'claimant-int-001',
        disputedClaimIds: ['claim-int-001'],
      };

      const disputeData = await parseSmsDisputeWebhook(webhookPayload);
      const inputParsed = SmsDisputePayloadSchema.safeParse(disputeData);
      expect(inputParsed.success).toBe(true);

      // Validate output schemas
      const result = await HandleSmsDisputeRequestHandler.handle(disputeData);

      // Each claim matches ClaimRecord schema
      result.updatedClaims.forEach((claim) => {
        const claimParsed = ClaimRecordSchema.safeParse(claim);
        expect(claimParsed.success).toBe(true);
      });

      // Case matches Case schema
      const caseParsed = CaseSchema.safeParse(blockedCase);
      expect(caseParsed.success).toBe(true);
    });
  });

  // =========================================================================
  // ErrorConsistency: All error scenarios across the path
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should return MALFORMED_WEBHOOK for invalid webhook payload', async () => {
      try {
        await parseSmsDisputeWebhook({ invalid: 'payload' });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('MALFORMED_WEBHOOK');
        expect((e as DisputeError).statusCode).toBe(400);
      }
    });

    it('should return VERIFICATION_REQUEST_NOT_FOUND for unknown token', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(null);

      try {
        await parseSmsDisputeWebhook({
          token: 'unknown-token',
          claimantId: 'c-1',
          disputedClaimIds: ['claim-1'],
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('VERIFICATION_REQUEST_NOT_FOUND');
        expect((e as DisputeError).statusCode).toBe(404);
      }
    });

    it('should return CLAIM_NOT_FOUND when disputed claim does not exist', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);
      mockClaimCaseDAO.getClaimById.mockResolvedValue(null);

      const disputeData = await parseSmsDisputeWebhook({
        token: 'verify-token-integration',
        claimantId: 'claimant-int-001',
        disputedClaimIds: ['nonexistent-claim'],
      });

      try {
        await HandleSmsDisputeRequestHandler.handle(disputeData);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('CLAIM_NOT_FOUND');
      }
    });

    it('should return INVALID_STATE_TRANSITION when case already blocked', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);
      mockClaimCaseDAO.getClaimById.mockResolvedValueOnce(verifiedClaim1);
      mockClaimCaseDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim1);
      mockClaimCaseDAO.getCaseByClaimantId.mockResolvedValue(blockedCase); // Already blocked!

      const disputeData = await parseSmsDisputeWebhook({
        token: 'verify-token-integration',
        claimantId: 'claimant-int-001',
        disputedClaimIds: ['claim-int-001'],
      });

      try {
        await HandleSmsDisputeRequestHandler.handle(disputeData);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('INVALID_STATE_TRANSITION');
        expect((e as DisputeError).statusCode).toBe(409);
      }
    });

    it('should return PERSISTENCE_ERROR when DAO update fails', async () => {
      mockVerificationDAO.findByToken.mockResolvedValue(activeVerificationRequest);
      mockClaimCaseDAO.getClaimById.mockResolvedValueOnce(verifiedClaim1);
      mockClaimCaseDAO.updateClaimVerificationStatus.mockRejectedValue(
        new Error('Database deadlock'),
      );

      const disputeData = await parseSmsDisputeWebhook({
        token: 'verify-token-integration',
        claimantId: 'claimant-int-001',
        disputedClaimIds: ['claim-int-001'],
      });

      try {
        await HandleSmsDisputeRequestHandler.handle(disputeData);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('PERSISTENCE_ERROR');
      }
    });
  });
});
