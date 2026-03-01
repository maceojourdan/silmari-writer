/**
 * step1.detectEligibility.test.ts - Step 1: Detect unverified key claims
 *
 * TLA+ Properties:
 * - Reachability: Seed claims table with 4 categories, all unverified → eligible: true + claims array
 * - TypeInvariant: eligible is boolean, claims is array of ClaimRecord
 * - ErrorConsistency: Missing required category → ClaimEligibilityError
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
  },
}));

import { VerificationService } from '../VerificationService';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const sessionId = 'session-321-test';

function createClaimRecord(overrides: Partial<ClaimRecord> = {}): ClaimRecord {
  return {
    id: `claim-${Math.random().toString(36).substring(7)}`,
    sessionId,
    category: 'metrics',
    status: 'unverified',
    contactPhone: '+15551234567',
    contactMethod: 'sms',
    content: 'Increased revenue by 40%',
    verifiedAt: null,
    createdAt: now,
    updatedAt: now,
    ...overrides,
  };
}

function createAllCategoryClaims(): ClaimRecord[] {
  return [
    createClaimRecord({ id: 'claim-metrics', category: 'metrics', content: 'Increased revenue by 40%' }),
    createClaimRecord({ id: 'claim-scope', category: 'scope', content: 'Managed team of 12 engineers' }),
    createClaimRecord({ id: 'claim-production', category: 'production', content: 'Deployed to 3 regions' }),
    createClaimRecord({ id: 'claim-security', category: 'security', content: 'Implemented SOC2 compliance' }),
  ];
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.detectEligibility — Step 1: Detect unverified key claims', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return eligible: true with claims when all 4 categories are present and unverified', async () => {
      const allClaims = createAllCategoryClaims();
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(allClaims);

      const result = await VerificationService.detectEligibility(sessionId);

      expect(result.eligible).toBe(true);
      expect(result.claims).toHaveLength(4);
    });

    it('should return all claim records in the result', async () => {
      const allClaims = createAllCategoryClaims();
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(allClaims);

      const result = await VerificationService.detectEligibility(sessionId);

      expect(result.claims).toEqual(allClaims);
    });

    it('should call ClaimDAO.getUnverifiedClaimsBySession with sessionId', async () => {
      const allClaims = createAllCategoryClaims();
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(allClaims);

      await VerificationService.detectEligibility(sessionId);

      expect(mockClaimDAO.getUnverifiedClaimsBySession).toHaveBeenCalledWith(sessionId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return eligible as boolean', async () => {
      const allClaims = createAllCategoryClaims();
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(allClaims);

      const result = await VerificationService.detectEligibility(sessionId);

      expect(typeof result.eligible).toBe('boolean');
    });

    it('should return claims as array of ClaimRecord type', async () => {
      const allClaims = createAllCategoryClaims();
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(allClaims);

      const result = await VerificationService.detectEligibility(sessionId);

      expect(Array.isArray(result.claims)).toBe(true);
      for (const claim of result.claims) {
        const parsed = ClaimRecordSchema.safeParse(claim);
        expect(parsed.success).toBe(true);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw ClaimEligibilityError when a required category is missing', async () => {
      // Missing 'security' category
      const incompleteClaims = [
        createClaimRecord({ id: 'claim-metrics', category: 'metrics' }),
        createClaimRecord({ id: 'claim-scope', category: 'scope' }),
        createClaimRecord({ id: 'claim-production', category: 'production' }),
      ];
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(incompleteClaims);

      try {
        await VerificationService.detectEligibility(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('CLAIM_ELIGIBILITY_ERROR');
      }
    });

    it('should throw ClaimEligibilityError when no claims exist', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([]);

      try {
        await VerificationService.detectEligibility(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('CLAIM_ELIGIBILITY_ERROR');
      }
    });

    it('should include missing categories in the error message', async () => {
      const incompleteClaims = [
        createClaimRecord({ id: 'claim-metrics', category: 'metrics' }),
      ];
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue(incompleteClaims);

      try {
        await VerificationService.detectEligibility(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as VerificationError).message).toContain('scope');
        expect((e as VerificationError).message).toContain('production');
        expect((e as VerificationError).message).toContain('security');
      }
    });
  });
});
