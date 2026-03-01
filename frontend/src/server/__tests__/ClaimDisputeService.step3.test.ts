/**
 * ClaimDisputeService.step3.test.ts - Tests for marking disputed claims as not_verified.
 *
 * Step 3 of Path 322: Mark disputed claims as not verified.
 *
 * TLA+ properties:
 * - Reachability: Seed verified claims → call handleDispute → claims updated to not_verified.
 * - TypeInvariant: Returned entities conform to ClaimRecord type.
 * - ErrorConsistency:
 *   - Claim not found → throw DisputeErrors.CLAIM_NOT_FOUND.
 *   - DAO update fails → throw DisputeErrors.PERSISTENCE_ERROR.
 *
 * Resource: db-h2s4 (service)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimRecordSchema } from '@/server/data_structures/ClaimRecord';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';
import type { Case } from '@/server/data_structures/Case';
import { DisputeError } from '@/server/error_definitions/DisputeErrors';

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

const verifiedClaim1: ClaimRecord = {
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

const verifiedClaim2: ClaimRecord = {
  id: 'claim-002',
  sessionId: 'session-001',
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

const seedCase: Case = {
  id: 'case-001',
  claimantId: 'claimant-001',
  sessionId: 'session-001',
  drafting_status: 'drafting_allowed',
  createdAt: now,
  updatedAt: now,
};

const blockedCase: Case = {
  ...seedCase,
  drafting_status: 'blocked_due_to_unverified_claims',
  updatedAt: now,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ClaimDisputeService — Step 3: Mark disputed claims', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // Reachability
  // =========================================================================

  describe('Reachability', () => {
    it('should update disputed claims to not_verified status', async () => {
      // Seed: verified claims exist
      mockDAO.getClaimById
        .mockResolvedValueOnce(verifiedClaim1)
        .mockResolvedValueOnce(verifiedClaim2);

      mockDAO.updateClaimVerificationStatus
        .mockResolvedValueOnce(disputedClaim1)
        .mockResolvedValueOnce(disputedClaim2);

      mockDAO.getCaseByClaimantId.mockResolvedValue(seedCase);
      mockDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      const result = await ClaimDisputeService.handleDispute(
        'claimant-001',
        ['claim-001', 'claim-002'],
      );

      // Assert claims are updated
      expect(result.updatedClaims).toHaveLength(2);
      expect(result.updatedClaims[0].status).toBe('not_verified');
      expect(result.updatedClaims[1].status).toBe('not_verified');
    });

    it('should call updateClaimVerificationStatus for each disputed claim', async () => {
      mockDAO.getClaimById
        .mockResolvedValueOnce(verifiedClaim1)
        .mockResolvedValueOnce(verifiedClaim2);

      mockDAO.updateClaimVerificationStatus
        .mockResolvedValueOnce(disputedClaim1)
        .mockResolvedValueOnce(disputedClaim2);

      mockDAO.getCaseByClaimantId.mockResolvedValue(seedCase);
      mockDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      await ClaimDisputeService.handleDispute('claimant-001', ['claim-001', 'claim-002']);

      expect(mockDAO.updateClaimVerificationStatus).toHaveBeenCalledTimes(2);
      expect(mockDAO.updateClaimVerificationStatus).toHaveBeenCalledWith(
        'claim-001',
        'not_verified',
        expect.any(String),
      );
      expect(mockDAO.updateClaimVerificationStatus).toHaveBeenCalledWith(
        'claim-002',
        'not_verified',
        expect.any(String),
      );
    });

    it('should record dispute metadata (disputedAt timestamp)', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim1);
      mockDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim1);
      mockDAO.getCaseByClaimantId.mockResolvedValue(seedCase);
      mockDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      const result = await ClaimDisputeService.handleDispute('claimant-001', ['claim-001']);

      expect(result.updatedClaims[0].disputedAt).toBeTruthy();
    });
  });

  // =========================================================================
  // TypeInvariant
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should return entities conforming to ClaimRecord type', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim1);
      mockDAO.updateClaimVerificationStatus.mockResolvedValueOnce(disputedClaim1);
      mockDAO.getCaseByClaimantId.mockResolvedValue(seedCase);
      mockDAO.updateCaseDraftingStatus.mockResolvedValue(blockedCase);

      const result = await ClaimDisputeService.handleDispute('claimant-001', ['claim-001']);

      result.updatedClaims.forEach((claim) => {
        const parsed = ClaimRecordSchema.safeParse(claim);
        expect(parsed.success).toBe(true);
      });
    });
  });

  // =========================================================================
  // ErrorConsistency
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should throw CLAIM_NOT_FOUND if claim does not exist', async () => {
      mockDAO.getClaimById.mockResolvedValue(null);

      try {
        await ClaimDisputeService.handleDispute('claimant-001', ['nonexistent-claim']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('CLAIM_NOT_FOUND');
      }
    });

    it('should throw PERSISTENCE_ERROR if DAO getClaimById fails', async () => {
      mockDAO.getClaimById.mockRejectedValue(new Error('DB connection lost'));

      try {
        await ClaimDisputeService.handleDispute('claimant-001', ['claim-001']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('PERSISTENCE_ERROR');
      }
    });

    it('should throw PERSISTENCE_ERROR if DAO update fails', async () => {
      mockDAO.getClaimById.mockResolvedValueOnce(verifiedClaim1);
      mockDAO.updateClaimVerificationStatus.mockRejectedValue(new Error('Deadlock'));

      try {
        await ClaimDisputeService.handleDispute('claimant-001', ['claim-001']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('PERSISTENCE_ERROR');
      }
    });

    it('should abort remaining updates if any claim update fails', async () => {
      mockDAO.getClaimById
        .mockResolvedValueOnce(verifiedClaim1)
        .mockResolvedValueOnce(verifiedClaim2);

      // First update succeeds, second fails
      mockDAO.updateClaimVerificationStatus
        .mockResolvedValueOnce(disputedClaim1)
        .mockRejectedValueOnce(new Error('Deadlock'));

      try {
        await ClaimDisputeService.handleDispute('claimant-001', ['claim-001', 'claim-002']);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DisputeError);
        expect((e as DisputeError).code).toBe('PERSISTENCE_ERROR');
        // Should not have tried to update case
        expect(mockDAO.getCaseByClaimantId).not.toHaveBeenCalled();
      }
    });
  });
});
