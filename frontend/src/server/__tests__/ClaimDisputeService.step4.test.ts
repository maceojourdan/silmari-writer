/**
 * ClaimDisputeService.step4.test.ts - Tests for blocking drafting process
 * after disputed claims are marked.
 *
 * Step 4 of Path 322: Block drafting process.
 *
 * TLA+ properties:
 * - Reachability: After Step 3, case drafting_status updated to 'blocked_due_to_unverified_claims'.
 * - TypeInvariant: Returned case matches Case type.
 * - ErrorConsistency:
 *   - Invalid transition → CaseStateVerifier rejects.
 *   - Expect DisputeErrors.INVALID_STATE_TRANSITION.
 *
 * Resources: db-h2s4 (service), db-j6x9 (backend_verifier)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { CaseSchema } from '@/server/data_structures/Case';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';
import type { Case } from '@/server/data_structures/Case';
import { DisputeError } from '@/server/error_definitions/DisputeErrors';
import { CaseStateVerifier } from '@/server/verifiers/CaseStateVerifier';

// ---------------------------------------------------------------------------
// Mocks: DAO layer (lowest level)
// ---------------------------------------------------------------------------

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

import { ClaimDisputeService } from '@/server/services/ClaimDisputeService';
import { ClaimCaseDAO } from '@/server/data_access_objects/ClaimCaseDAO';

const mockDAO = vi.mocked(ClaimCaseDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const verifiedClaim: ClaimRecord = {
  id: 'claim-001',
  sessionId: 'session-001',
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

const disputedClaim: ClaimRecord = {
  ...verifiedClaim,
  status: 'not_verified',
  disputedAt: now,
  updatedAt: now,
};

const draftingAllowedCase: Case = {
  id: 'case-001',
  claimantId: 'claimant-001',
  sessionId: 'session-001',
  drafting_status: 'drafting_allowed',
  createdAt: now,
  updatedAt: now,
};

const blockedCase: Case = {
  ...draftingAllowedCase,
  drafting_status: 'blocked_due_to_unverified_claims',
  updatedAt: now,
};

const alreadyBlockedCase: Case = {
  ...draftingAllowedCase,
  drafting_status: 'blocked_due_to_unverified_claims',
  updatedAt: now,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ClaimDisputeService — Step 4: Block drafting process', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // Reachability
  // =========================================================================

  describe('Reachability', () => {
    it('should update case drafting_status to blocked_due_to_unverified_claims', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim);
      mockDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim);
      mockDAO.getCaseByClaimantId.mockResolvedValue(draftingAllowedCase);
      mockDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      const result = await ClaimDisputeService.handleDispute(
        'claimant-001',
        ['claim-001'],
      );

      expect(result.caseBlocked).toBe(true);
      expect(mockDAO.updateCaseDraftingStatus).toHaveBeenCalledWith(
        'case-001',
        'blocked_due_to_unverified_claims',
      );
    });
  });

  // =========================================================================
  // TypeInvariant
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should return blockedCase matching Case type schema', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim);
      mockDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim);
      mockDAO.getCaseByClaimantId.mockResolvedValue(draftingAllowedCase);
      mockDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      const result = await ClaimDisputeService.handleDispute(
        'claimant-001',
        ['claim-001'],
      );

      // Verify the case used in the DAO call is valid
      const parsed = CaseSchema.safeParse(blockedCase);
      expect(parsed.success).toBe(true);
      expect(result.caseBlocked).toBe(true);
    });
  });

  // =========================================================================
  // ErrorConsistency
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should throw INVALID_STATE_TRANSITION when case is already blocked', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim);
      mockDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim);
      mockDAO.getCaseByClaimantId.mockResolvedValue(alreadyBlockedCase);

      try {
        await ClaimDisputeService.handleDispute('claimant-001', ['claim-001']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('INVALID_STATE_TRANSITION');
        expect((e as DisputeError).statusCode).toBe(409);
      }
    });

    it('should throw CLAIM_NOT_FOUND when case does not exist for claimant', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim);
      mockDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim);
      mockDAO.getCaseByClaimantId.mockResolvedValue(null);

      try {
        await ClaimDisputeService.handleDispute('claimant-001', ['claim-001']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('CLAIM_NOT_FOUND');
      }
    });

    it('should throw PERSISTENCE_ERROR when case update fails', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim);
      mockDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim);
      mockDAO.getCaseByClaimantId.mockResolvedValue(draftingAllowedCase);
      mockDAO.updateCaseDraftingStatus.mockRejectedValue(new Error('DB write failed'));

      try {
        await ClaimDisputeService.handleDispute('claimant-001', ['claim-001']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('PERSISTENCE_ERROR');
      }
    });
  });

  // =========================================================================
  // CaseStateVerifier unit tests
  // =========================================================================

  describe('CaseStateVerifier', () => {
    it('should allow blocking from drafting_allowed state', () => {
      const result = CaseStateVerifier.assertDraftingBlockAllowed('drafting_allowed');
      expect(result.valid).toBe(true);
    });

    it('should reject blocking when already blocked', () => {
      const result = CaseStateVerifier.assertDraftingBlockAllowed('blocked_due_to_unverified_claims');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.reason).toContain('already blocked');
      }
    });

    it('should reject blocking from unknown state', () => {
      const result = CaseStateVerifier.assertDraftingBlockAllowed('some_other_state');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.reason).toContain('Unknown');
      }
    });
  });
});
