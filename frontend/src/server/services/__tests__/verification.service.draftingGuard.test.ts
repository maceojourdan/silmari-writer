/**
 * verification.service.draftingGuard.test.ts - Step 5: Prevent Drafting From Starting
 *
 * TLA+ Properties:
 * - Reachability: After failure recorded → startDrafting returns { draftingAllowed: false, reason: "VERIFICATION_FAILED" }
 * - TypeInvariant: Return type is { draftingAllowed: boolean; reason?: string }
 * - ErrorConsistency: Drafting state already IN_PROGRESS → state updated to BLOCKED + log entry
 *
 * Resource: db-h2s4 (service)
 * Path: 323-fail-verification-when-no-contact-method
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StartDraftingResultSchema } from '@/server/data_structures/VerificationAttempt';
import type { VerificationAttempt } from '@/server/data_structures/VerificationAttempt';

// Mock all dependencies
vi.mock('@/server/logging/verificationLogger', () => ({
  verificationLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/VerificationDAO', () => ({
  VerificationDAO: {
    getClaimantById: vi.fn(),
    createVerificationAttempt: vi.fn(),
    getLatestVerificationAttempt: vi.fn(),
    updateDraftingStatus: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getUnverifiedClaimsBySession: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    updateStatusToVerified: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/VerificationRequestDAO', () => ({
  VerificationRequestDAO: {
    create: vi.fn(),
    findByToken: vi.fn(),
    findBySessionId: vi.fn(),
    updateStatus: vi.fn(),
    logDeliveryAttempt: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
  },
}));

vi.mock('@/server/verifiers/ContactMethodVerifier', () => ({
  ContactMethodVerifier: {
    validate: vi.fn(),
  },
}));

import { VerificationService } from '../VerificationService';
import { VerificationDAO } from '@/server/data_access_objects/VerificationDAO';
import { verificationLogger } from '@/server/logging/verificationLogger';

const mockDAO = vi.mocked(VerificationDAO);
const mockLogger = vi.mocked(verificationLogger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const claimantId = '550e8400-e29b-41d4-a716-446655440000';

function createFailedAttempt(overrides?: Partial<VerificationAttempt>): VerificationAttempt {
  return {
    id: 'va-001',
    claimantId,
    status: 'FAILED',
    reason: 'MISSING_CONTACT_METHOD',
    createdAt: now,
    updatedAt: now,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.startDrafting — Step 5: Prevent Drafting From Starting', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return draftingAllowed=false when latest verification attempt is FAILED', async () => {
      mockDAO.getLatestVerificationAttempt.mockResolvedValue(createFailedAttempt());

      const result = await VerificationService.startDrafting(claimantId);

      expect(result).toEqual({
        draftingAllowed: false,
        reason: 'VERIFICATION_FAILED',
      });
    });

    it('should fetch the latest verification attempt for the claimant', async () => {
      mockDAO.getLatestVerificationAttempt.mockResolvedValue(createFailedAttempt());

      await VerificationService.startDrafting(claimantId);

      expect(mockDAO.getLatestVerificationAttempt).toHaveBeenCalledWith(claimantId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object matching StartDraftingResult schema', async () => {
      mockDAO.getLatestVerificationAttempt.mockResolvedValue(createFailedAttempt());

      const result = await VerificationService.startDrafting(claimantId);

      const parsed = StartDraftingResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should update drafting status to BLOCKED when draftingStatus is IN_PROGRESS', async () => {
      mockDAO.getLatestVerificationAttempt.mockResolvedValue(
        createFailedAttempt({ draftingStatus: 'IN_PROGRESS' }),
      );
      mockDAO.updateDraftingStatus.mockResolvedValue(undefined);

      await VerificationService.startDrafting(claimantId);

      expect(mockDAO.updateDraftingStatus).toHaveBeenCalledWith(
        'va-001',
        'BLOCKED',
      );
    });

    it('should log corrective action when drafting was already IN_PROGRESS', async () => {
      mockDAO.getLatestVerificationAttempt.mockResolvedValue(
        createFailedAttempt({ draftingStatus: 'IN_PROGRESS' }),
      );
      mockDAO.updateDraftingStatus.mockResolvedValue(undefined);

      await VerificationService.startDrafting(claimantId);

      expect(mockLogger.warn).toHaveBeenCalled();
    });

    it('should return draftingAllowed=false even when IN_PROGRESS was blocked', async () => {
      mockDAO.getLatestVerificationAttempt.mockResolvedValue(
        createFailedAttempt({ draftingStatus: 'IN_PROGRESS' }),
      );
      mockDAO.updateDraftingStatus.mockResolvedValue(undefined);

      const result = await VerificationService.startDrafting(claimantId);

      expect(result.draftingAllowed).toBe(false);
    });
  });
});
