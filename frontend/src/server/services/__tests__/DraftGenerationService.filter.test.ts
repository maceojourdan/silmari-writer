/**
 * DraftGenerationService.filter.test.ts — Step 4: Retrieve and filter confirmed claims
 *
 * TLA+ Properties:
 * - Reachability: DAO returns mix of confirmed/unconfirmed/rejected → only confirmed returned
 * - TypeInvariant: Each item matches CaseClaim type from Claim.ts
 * - ErrorConsistency: DAO throws → DraftErrors326.DataAccessError
 * - Edge: DAO returns only unconfirmed/rejected → expect empty array
 *
 * Resource: db-h2s4 (service)
 * Path: 326-generate-draft-with-only-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { CaseClaimSchema } from '@/server/data_structures/Claim';
import type { CaseClaim } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// Mock the ClaimDAO
vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getClaimsByCaseId: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    getUnverifiedClaimsBySession: vi.fn(),
    updateStatusToVerified: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

import { DraftGenerationService } from '../DraftGenerationService';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validCaseId = 'case-abc-123';

function createCaseClaim(overrides: Partial<CaseClaim> = {}): CaseClaim {
  return {
    id: `claim-${Math.random().toString(36).slice(2, 8)}`,
    caseId: validCaseId,
    text: 'A test claim',
    status: 'confirmed',
    metadata: undefined,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerationService — Step 4: Retrieve and filter confirmed claims (path 326)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return only confirmed claims from a mix of statuses', async () => {
      const confirmed1 = createCaseClaim({ status: 'confirmed', text: 'Confirmed A' });
      const confirmed2 = createCaseClaim({ status: 'confirmed', text: 'Confirmed B' });
      const unconfirmed = createCaseClaim({ status: 'unconfirmed', text: 'Unconfirmed' });
      const rejected = createCaseClaim({ status: 'rejected', text: 'Rejected' });

      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([
        confirmed1,
        confirmed2,
        unconfirmed,
        rejected,
      ]);

      const result = await DraftGenerationService.getConfirmedClaimsForCase(validCaseId);

      expect(result).toHaveLength(2);
      expect(result.every((c) => c.status === 'confirmed')).toBe(true);
      expect(result.map((c) => c.text)).toEqual(['Confirmed A', 'Confirmed B']);
    });

    it('should pass caseId to the DAO', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([
        createCaseClaim({ status: 'confirmed' }),
      ]);

      await DraftGenerationService.getConfirmedClaimsForCase(validCaseId);

      expect(mockClaimDAO.getClaimsByCaseId).toHaveBeenCalledWith(validCaseId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return array conforming to CaseClaim schema', async () => {
      const confirmedClaim = createCaseClaim({ status: 'confirmed' });
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([confirmedClaim]);

      const result = await DraftGenerationService.getConfirmedClaimsForCase(validCaseId);

      result.forEach((claim) => {
        const parsed = CaseClaimSchema.safeParse(claim);
        expect(parsed.success).toBe(true);
      });
    });

    it('should preserve all CaseClaim fields in the output', async () => {
      const confirmedClaim = createCaseClaim({
        status: 'confirmed',
        text: 'Specific claim text',
        metadata: { key: 'value' },
      });
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([confirmedClaim]);

      const result = await DraftGenerationService.getConfirmedClaimsForCase(validCaseId);

      expect(result[0]).toMatchObject({
        status: 'confirmed',
        text: 'Specific claim text',
        metadata: { key: 'value' },
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw DATA_ACCESS_ERROR when DAO throws', async () => {
      mockClaimDAO.getClaimsByCaseId.mockRejectedValueOnce(
        new Error('Database connection failed'),
      );

      await expect(
        DraftGenerationService.getConfirmedClaimsForCase(validCaseId),
      ).rejects.toThrow(DraftError);

      try {
        mockClaimDAO.getClaimsByCaseId.mockRejectedValueOnce(
          new Error('Database connection failed'),
        );
        await DraftGenerationService.getConfirmedClaimsForCase(validCaseId);
      } catch (e) {
        expect((e as DraftError).code).toBe('DATA_ACCESS_ERROR');
        expect((e as DraftError).statusCode).toBe(500);
      }
    });
  });

  // -------------------------------------------------------------------------
  // Edge: No confirmed claims
  // -------------------------------------------------------------------------

  describe('Edge — No confirmed claims', () => {
    it('should return empty array when all claims are unconfirmed/rejected', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([
        createCaseClaim({ status: 'unconfirmed' }),
        createCaseClaim({ status: 'rejected' }),
      ]);

      const result = await DraftGenerationService.getConfirmedClaimsForCase(validCaseId);

      expect(result).toEqual([]);
    });

    it('should return empty array when no claims exist', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([]);

      const result = await DraftGenerationService.getConfirmedClaimsForCase(validCaseId);

      expect(result).toEqual([]);
    });
  });
});
