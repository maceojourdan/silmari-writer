/**
 * step4.markVerified.test.ts - Step 4: Mark claims as verified
 *
 * TLA+ Properties:
 * - Reachability: Confirmed result → each claim.status === 'verified'
 * - TypeInvariant: Updated records contain verifiedAt: Date string
 * - ErrorConsistency: Mock DAO update failure → DataAccessError, drafting not enabled
 *
 * Resource: db-h2s4 (service)
 * Path: 321-verify-key-claims-via-voice-or-sms
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import { ClaimRecordSchema } from '@/server/data_structures/ClaimRecord';
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
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const verifiedAt = new Date().toISOString();
const sessionId = 'session-321-step4';

function createUnverifiedClaims(): ClaimRecord[] {
  return [
    { id: 'claim-m', sessionId, category: 'metrics', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Revenue +40%', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-s', sessionId, category: 'scope', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'Team of 12', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-p', sessionId, category: 'production', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: '3 regions', verifiedAt: null, createdAt: now, updatedAt: now },
    { id: 'claim-sec', sessionId, category: 'security', status: 'unverified', contactPhone: '+15551234567', contactMethod: 'sms', content: 'SOC2', verifiedAt: null, createdAt: now, updatedAt: now },
  ];
}

function createVerifiedClaims(): ClaimRecord[] {
  return createUnverifiedClaims().map(c => ({
    ...c,
    status: 'verified' as const,
    verifiedAt,
    updatedAt: verifiedAt,
  }));
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.markClaimsVerified — Step 4: Mark claims as verified', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(createUnverifiedClaims());
    mockClaimDAO.updateStatusToVerified.mockResolvedValue(createVerifiedClaims());
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return all claims with status === verified', async () => {
      const result = await VerificationService.markClaimsVerified(sessionId);

      for (const claim of result) {
        expect(claim.status).toBe('verified');
      }
    });

    it('should call ClaimDAO.updateStatusToVerified with correct claim IDs', async () => {
      await VerificationService.markClaimsVerified(sessionId);

      expect(mockClaimDAO.updateStatusToVerified).toHaveBeenCalledWith(
        ['claim-m', 'claim-s', 'claim-p', 'claim-sec'],
      );
    });

    it('should return 4 verified claims', async () => {
      const result = await VerificationService.markClaimsVerified(sessionId);

      expect(result).toHaveLength(4);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return records with verifiedAt as a date string', async () => {
      const result = await VerificationService.markClaimsVerified(sessionId);

      for (const claim of result) {
        expect(claim.verifiedAt).toBeDefined();
        expect(typeof claim.verifiedAt).toBe('string');
        // Should be a valid date string
        expect(new Date(claim.verifiedAt!).toISOString()).toBe(claim.verifiedAt);
      }
    });

    it('should return records conforming to ClaimRecord schema', async () => {
      const result = await VerificationService.markClaimsVerified(sessionId);

      for (const claim of result) {
        const parsed = ClaimRecordSchema.safeParse(claim);
        expect(parsed.success).toBe(true);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw DataAccessError when DAO update fails', async () => {
      mockClaimDAO.updateStatusToVerified.mockRejectedValue(
        new Error('Database connection lost'),
      );

      try {
        await VerificationService.markClaimsVerified(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('DATA_ACCESS_ERROR');
      }
    });

    it('should throw DataAccessError when getUnverifiedClaims fails', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockRejectedValue(
        new Error('Table not found'),
      );

      try {
        await VerificationService.markClaimsVerified(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('DATA_ACCESS_ERROR');
      }
    });

    it('should have retryable flag set to true on DataAccessError', async () => {
      mockClaimDAO.updateStatusToVerified.mockRejectedValue(
        new Error('Temporary failure'),
      );

      try {
        await VerificationService.markClaimsVerified(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as VerificationError).retryable).toBe(true);
      }
    });
  });
});
