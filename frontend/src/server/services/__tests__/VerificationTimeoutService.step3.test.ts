/**
 * Step 3 Tests: Enforce claims remain unverified and drafting on hold
 *
 * Resource: db-h2s4 (service)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * TLA+ Properties tested:
 * - Reachability: claim → 'UNVERIFIED', drafting → 'On Hold'
 * - TypeInvariant: result is { claim: Claim; drafting: DraftingWorkflow }[]
 * - ErrorConsistency: missing entity → DomainIntegrityError; validation fail → ValidationError
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationTimeoutService } from '@/server/services/VerificationTimeoutService';
import { DomainError } from '@/server/error_definitions/DomainErrors';

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

vi.mock('@/server/settings/verificationTimeout', () => ({
  getVerificationTimeoutMs: vi.fn(),
}));

vi.mock('@/server/data_access_objects/VerificationRequestDAO', () => ({
  VerificationRequestDAO: {
    findPendingUnresponded: vi.fn(),
    updateStatusIfUnresponded: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    findById: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/DraftingWorkflowDAO', () => ({
  DraftingWorkflowDAO: {
    findByClaimId: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

vi.mock('@/server/verifiers/ClaimDraftingStateVerifier', () => ({
  ClaimDraftingStateVerifier: {
    validate: vi.fn(),
    validateClaimStatus: vi.fn(),
    validateDraftingStatus: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { DraftingWorkflowDAO } from '@/server/data_access_objects/DraftingWorkflowDAO';
import { ClaimDraftingStateVerifier } from '@/server/verifiers/ClaimDraftingStateVerifier';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';
import type { Claim } from '@/server/data_structures/Claim';
import type { DraftingWorkflow } from '@/server/data_structures/DraftingWorkflow';

const mockFindById = vi.mocked(ClaimDAO.findById);
const mockUpdateClaimStatus = vi.mocked(ClaimDAO.updateStatus);
const mockFindByClaimId = vi.mocked(DraftingWorkflowDAO.findByClaimId);
const mockUpdateDraftingStatus = vi.mocked(DraftingWorkflowDAO.updateStatus);
const mockVerifierValidate = vi.mocked(ClaimDraftingStateVerifier.validate);

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

function makeTimedOutRequest(overrides: Partial<VerificationRequest> = {}): VerificationRequest {
  return {
    id: 'vr-001',
    sessionId: 'session-001',
    status: 'timed_out',
    attemptCount: 1,
    token: 'token-abc',
    claimIds: ['claim-001'],
    contactPhone: '+15551234567',
    contactMethod: 'sms',
    respondedAt: null,
    createdAt: new Date(Date.now() - 10 * 60 * 1000).toISOString(),
    updatedAt: new Date().toISOString(),
    ...overrides,
  };
}

function makeClaim(overrides: Partial<Claim> = {}): Claim {
  return {
    id: 'claim-001',
    content: 'Test claim content',
    status: 'CONFIRMED',
    smsOptIn: true,
    phoneNumber: '+15551234567',
    truth_checks: [],
    created_at: new Date().toISOString(),
    updated_at: new Date().toISOString(),
    ...overrides,
  };
}

function makeDraftingWorkflow(overrides: Partial<DraftingWorkflow> = {}): DraftingWorkflow {
  return {
    id: 'dw-001',
    claimId: 'claim-001',
    status: 'Ready',
    createdAt: new Date().toISOString(),
    updatedAt: new Date().toISOString(),
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationTimeoutService.enforceUnverifiedAndOnHold', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -----------------------------------------------------------------------
  // Reachability
  // -----------------------------------------------------------------------

  describe('Reachability', () => {
    it('should update claim to Unverified and drafting to On Hold', async () => {
      const record = makeTimedOutRequest();
      const claim = makeClaim({ status: 'CONFIRMED' });
      const drafting = makeDraftingWorkflow({ status: 'Ready' });
      const updatedClaim = { ...claim, status: 'UNVERIFIED' as const };
      const updatedDrafting = { ...drafting, status: 'On Hold' as const, reason: 'Verification timed out' };

      mockFindById.mockResolvedValue(claim);
      mockFindByClaimId.mockResolvedValue(drafting);
      mockVerifierValidate.mockReturnValue(undefined);
      mockUpdateClaimStatus.mockResolvedValue(updatedClaim);
      mockUpdateDraftingStatus.mockResolvedValue(updatedDrafting);

      const result = await VerificationTimeoutService.enforceUnverifiedAndOnHold([record]);

      expect(result).toHaveLength(1);
      expect(result[0].claim.status).toBe('UNVERIFIED');
      expect(result[0].drafting.status).toBe('On Hold');

      expect(mockUpdateClaimStatus).toHaveBeenCalledWith('claim-001', 'UNVERIFIED');
      expect(mockUpdateDraftingStatus).toHaveBeenCalledWith(
        'dw-001',
        'On Hold',
        'Verification timed out',
      );
    });

    it('should handle records with multiple claim IDs', async () => {
      const record = makeTimedOutRequest({ claimIds: ['claim-001', 'claim-002'] });

      const claim1 = makeClaim({ id: 'claim-001' });
      const claim2 = makeClaim({ id: 'claim-002' });
      const dw1 = makeDraftingWorkflow({ id: 'dw-001', claimId: 'claim-001' });
      const dw2 = makeDraftingWorkflow({ id: 'dw-002', claimId: 'claim-002' });

      mockFindById
        .mockResolvedValueOnce(claim1)
        .mockResolvedValueOnce(claim2);
      mockFindByClaimId
        .mockResolvedValueOnce(dw1)
        .mockResolvedValueOnce(dw2);
      mockVerifierValidate.mockReturnValue(undefined);
      mockUpdateClaimStatus
        .mockResolvedValueOnce({ ...claim1, status: 'UNVERIFIED' })
        .mockResolvedValueOnce({ ...claim2, status: 'UNVERIFIED' });
      mockUpdateDraftingStatus
        .mockResolvedValueOnce({ ...dw1, status: 'On Hold', reason: 'Verification timed out' })
        .mockResolvedValueOnce({ ...dw2, status: 'On Hold', reason: 'Verification timed out' });

      const result = await VerificationTimeoutService.enforceUnverifiedAndOnHold([record]);

      expect(result).toHaveLength(2);
      expect(result[0].claim.status).toBe('UNVERIFIED');
      expect(result[1].claim.status).toBe('UNVERIFIED');
    });
  });

  // -----------------------------------------------------------------------
  // TypeInvariant
  // -----------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return { claim: Claim; drafting: DraftingWorkflow }', async () => {
      const record = makeTimedOutRequest();
      const claim = makeClaim();
      const drafting = makeDraftingWorkflow();

      mockFindById.mockResolvedValue(claim);
      mockFindByClaimId.mockResolvedValue(drafting);
      mockVerifierValidate.mockReturnValue(undefined);
      mockUpdateClaimStatus.mockResolvedValue({ ...claim, status: 'UNVERIFIED' });
      mockUpdateDraftingStatus.mockResolvedValue({ ...drafting, status: 'On Hold' });

      const result = await VerificationTimeoutService.enforceUnverifiedAndOnHold([record]);

      expect(result[0]).toHaveProperty('claim');
      expect(result[0]).toHaveProperty('drafting');
      expect(result[0].claim.status).toBe('UNVERIFIED');
      expect(result[0].drafting.status).toBe('On Hold');
    });
  });

  // -----------------------------------------------------------------------
  // ErrorConsistency
  // -----------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw DomainIntegrityError when claim is missing', async () => {
      const record = makeTimedOutRequest();
      mockFindById.mockResolvedValue(null);

      await expect(
        VerificationTimeoutService.enforceUnverifiedAndOnHold([record]),
      ).rejects.toThrow(DomainError);

      await expect(
        VerificationTimeoutService.enforceUnverifiedAndOnHold([record]),
      ).rejects.toMatchObject({
        code: 'DOMAIN_INTEGRITY_ERROR',
      });
    });

    it('should throw DomainIntegrityError when drafting workflow is missing', async () => {
      const record = makeTimedOutRequest();
      const claim = makeClaim();

      mockFindById.mockResolvedValue(claim);
      mockFindByClaimId.mockResolvedValue(null);

      await expect(
        VerificationTimeoutService.enforceUnverifiedAndOnHold([record]),
      ).rejects.toThrow(DomainError);

      await expect(
        VerificationTimeoutService.enforceUnverifiedAndOnHold([record]),
      ).rejects.toMatchObject({
        code: 'DOMAIN_INTEGRITY_ERROR',
      });
    });

    it('should throw ValidationError when verifier fails', async () => {
      const record = makeTimedOutRequest();
      const claim = makeClaim();
      const drafting = makeDraftingWorkflow();

      mockFindById.mockResolvedValue(claim);
      mockFindByClaimId.mockResolvedValue(drafting);

      const { DomainErrors } = await import('@/server/error_definitions/DomainErrors');
      mockVerifierValidate.mockImplementation(() => {
        throw DomainErrors.VALIDATION_ERROR('Invalid state transition');
      });

      await expect(
        VerificationTimeoutService.enforceUnverifiedAndOnHold([record]),
      ).rejects.toThrow(DomainError);

      await expect(
        VerificationTimeoutService.enforceUnverifiedAndOnHold([record]),
      ).rejects.toMatchObject({
        code: 'VALIDATION_ERROR',
      });
    });
  });
});
