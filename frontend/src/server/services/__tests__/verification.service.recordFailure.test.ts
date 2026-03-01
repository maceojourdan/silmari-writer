/**
 * verification.service.recordFailure.test.ts - Step 4: Record Verification Failure
 *
 * TLA+ Properties:
 * - Reachability: hasContactMethod=false → DAO creates record { status: "FAILED", reason: "MISSING_CONTACT_METHOD" }
 * - TypeInvariant: Persisted record matches VerificationAttempt schema
 * - ErrorConsistency: DAO throws → VERIFICATION_PERSISTENCE_FAILED + logger called
 *
 * Resource: db-h2s4 (service)
 * Path: 323-fail-verification-when-no-contact-method
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import { VerificationAttemptSchema } from '@/server/data_structures/VerificationAttempt';
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

function createFailedAttempt(): VerificationAttempt {
  return {
    id: 'va-001',
    claimantId,
    status: 'FAILED',
    reason: 'MISSING_CONTACT_METHOD',
    createdAt: now,
    updatedAt: now,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.recordVerificationFailure — Step 4: Record Verification Failure', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DAO.createVerificationAttempt with FAILED status and MISSING_CONTACT_METHOD reason', async () => {
      mockDAO.createVerificationAttempt.mockResolvedValue(createFailedAttempt());

      await VerificationService.recordVerificationFailure(
        claimantId,
        'MISSING_CONTACT_METHOD',
      );

      expect(mockDAO.createVerificationAttempt).toHaveBeenCalledWith(
        claimantId,
        'FAILED',
        'MISSING_CONTACT_METHOD',
      );
    });

    it('should return the persisted verification attempt', async () => {
      const expected = createFailedAttempt();
      mockDAO.createVerificationAttempt.mockResolvedValue(expected);

      const result = await VerificationService.recordVerificationFailure(
        claimantId,
        'MISSING_CONTACT_METHOD',
      );

      expect(result).toEqual(expected);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object matching the VerificationAttempt schema', async () => {
      mockDAO.createVerificationAttempt.mockResolvedValue(createFailedAttempt());

      const result = await VerificationService.recordVerificationFailure(
        claimantId,
        'MISSING_CONTACT_METHOD',
      );

      const parsed = VerificationAttemptSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw VERIFICATION_PERSISTENCE_FAILED when DAO throws', async () => {
      mockDAO.createVerificationAttempt.mockRejectedValue(
        new Error('DB connection lost'),
      );

      try {
        await VerificationService.recordVerificationFailure(
          claimantId,
          'MISSING_CONTACT_METHOD',
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('VERIFICATION_PERSISTENCE_FAILED');
      }
    });

    it('should log error when persistence fails', async () => {
      mockDAO.createVerificationAttempt.mockRejectedValue(
        new Error('DB connection lost'),
      );

      try {
        await VerificationService.recordVerificationFailure(
          claimantId,
          'MISSING_CONTACT_METHOD',
        );
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalled();
    });
  });
});
