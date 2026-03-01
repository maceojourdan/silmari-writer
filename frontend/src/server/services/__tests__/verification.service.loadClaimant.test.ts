/**
 * verification.service.loadClaimant.test.ts - Step 2: Load Claimant Data
 *
 * TLA+ Properties:
 * - Reachability: Mock DAO returns valid claimant → DAO.getClaimantById called
 * - TypeInvariant: Returned object matches Claimant type
 * - ErrorConsistency: DAO returns null → CLAIMANT_NOT_FOUND
 *
 * Resource: db-h2s4 (service)
 * Path: 323-fail-verification-when-no-contact-method
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import { ClaimantSchema } from '@/server/data_structures/Claimant';
import type { Claimant } from '@/server/data_structures/Claimant';

// Mock all DAOs and loggers
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

const mockDAO = vi.mocked(VerificationDAO);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const claimantId = '550e8400-e29b-41d4-a716-446655440000';

function createValidClaimant(): Claimant {
  return {
    id: claimantId,
    keyClaims: [
      { id: 'kc-1', category: 'metrics', content: 'Revenue +40%' },
      { id: 'kc-2', category: 'scope', content: 'Team of 12' },
    ],
    phone: null,
    smsOptIn: false,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.loadClaimant — Step 2: Load Claimant Data', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call VerificationDAO.getClaimantById with the claimant id', async () => {
      mockDAO.getClaimantById.mockResolvedValue(createValidClaimant());

      await VerificationService.loadClaimant(claimantId);

      expect(mockDAO.getClaimantById).toHaveBeenCalledWith(claimantId);
    });

    it('should return the claimant profile', async () => {
      const claimant = createValidClaimant();
      mockDAO.getClaimantById.mockResolvedValue(claimant);

      const result = await VerificationService.loadClaimant(claimantId);

      expect(result).toEqual(claimant);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object matching the Claimant schema', async () => {
      const claimant = createValidClaimant();
      mockDAO.getClaimantById.mockResolvedValue(claimant);

      const result = await VerificationService.loadClaimant(claimantId);

      const parsed = ClaimantSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw CLAIMANT_NOT_FOUND when DAO returns null', async () => {
      mockDAO.getClaimantById.mockResolvedValue(null);

      try {
        await VerificationService.loadClaimant(claimantId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('CLAIMANT_NOT_FOUND');
      }
    });
  });
});
