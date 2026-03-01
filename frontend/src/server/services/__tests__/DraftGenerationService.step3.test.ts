/**
 * DraftGenerationService.step3.test.ts - Step 3: Retrieve confirmed claims
 *
 * TLA+ Properties:
 * - Reachability: Seed DB with claims (confirmed + unconfirmed) → only confirmed passed to transform
 * - TypeInvariant: Returned array conforms to StoryClaim type
 * - ErrorConsistency: No claim set → CLAIM_SET_NOT_FOUND; No confirmed claims → NO_CONFIRMED_CLAIMS
 *
 * Resource: db-h2s4 (service)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoryClaimSchema } from '@/server/data_structures/StoryStructures';
import type { StoryClaim } from '@/server/data_structures/StoryStructures';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// Mock the StoryDAO
vi.mock('@/server/data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    getClaimsBySetId: vi.fn(),
    saveDraft: vi.fn(),
  },
}));

import { DraftGenerationService } from '../DraftGenerationService';
import { StoryDAO } from '@/server/data_access_objects/StoryDAO';

const mockStoryDAO = vi.mocked(StoryDAO);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validClaimSetId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';
const now = new Date().toISOString();

function createClaim(overrides: Partial<StoryClaim> = {}): StoryClaim {
  return {
    id: crypto.randomUUID(),
    claimSetId: validClaimSetId,
    content: 'A test claim',
    status: 'CONFIRMED',
    section: 'context',
    order: 0,
    createdAt: now,
    updatedAt: now,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerationService.retrieveConfirmedClaims — Step 3', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return only confirmed claims from a claim set', async () => {
      const confirmedClaim1 = createClaim({ status: 'CONFIRMED', content: 'Confirmed A' });
      const confirmedClaim2 = createClaim({ status: 'CONFIRMED', content: 'Confirmed B' });
      const unconfirmedClaim = createClaim({ status: 'UNCONFIRMED', content: 'Unconfirmed' });
      const pendingClaim = createClaim({ status: 'PENDING', content: 'Pending' });

      mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([
        confirmedClaim1,
        confirmedClaim2,
        unconfirmedClaim,
        pendingClaim,
      ]);

      const result = await DraftGenerationService.retrieveConfirmedClaims(validClaimSetId);

      expect(result).toHaveLength(2);
      expect(result.every((c) => c.status === 'CONFIRMED')).toBe(true);
      expect(result.map((c) => c.content)).toEqual(['Confirmed A', 'Confirmed B']);
    });

    it('should pass claimSetId to the DAO', async () => {
      mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([
        createClaim({ status: 'CONFIRMED' }),
      ]);

      await DraftGenerationService.retrieveConfirmedClaims(validClaimSetId);

      expect(mockStoryDAO.getClaimsBySetId).toHaveBeenCalledWith(validClaimSetId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return array conforming to StoryClaim schema', async () => {
      const confirmedClaim = createClaim({ status: 'CONFIRMED' });
      mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([confirmedClaim]);

      const result = await DraftGenerationService.retrieveConfirmedClaims(validClaimSetId);

      result.forEach((claim) => {
        const parsed = StoryClaimSchema.safeParse(claim);
        expect(parsed.success).toBe(true);
      });
    });

    it('should preserve all StoryClaim fields in the output', async () => {
      const confirmedClaim = createClaim({
        status: 'CONFIRMED',
        section: 'actions',
        order: 2,
        content: 'Specific claim content',
      });
      mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([confirmedClaim]);

      const result = await DraftGenerationService.retrieveConfirmedClaims(validClaimSetId);

      expect(result[0]).toMatchObject({
        status: 'CONFIRMED',
        section: 'actions',
        order: 2,
        content: 'Specific claim content',
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw CLAIM_SET_NOT_FOUND when claim set does not exist', async () => {
      mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce(null);

      await expect(
        DraftGenerationService.retrieveConfirmedClaims(validClaimSetId),
      ).rejects.toThrow(DraftError);

      try {
        mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce(null);
        await DraftGenerationService.retrieveConfirmedClaims(validClaimSetId);
      } catch (e) {
        expect((e as DraftError).code).toBe('CLAIM_SET_NOT_FOUND');
        expect((e as DraftError).statusCode).toBe(404);
      }
    });

    it('should throw NO_CONFIRMED_CLAIMS when all claims are unconfirmed', async () => {
      mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([
        createClaim({ status: 'UNCONFIRMED' }),
        createClaim({ status: 'PENDING' }),
      ]);

      await expect(
        DraftGenerationService.retrieveConfirmedClaims(validClaimSetId),
      ).rejects.toThrow(DraftError);

      try {
        mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([
          createClaim({ status: 'UNCONFIRMED' }),
        ]);
        await DraftGenerationService.retrieveConfirmedClaims(validClaimSetId);
      } catch (e) {
        expect((e as DraftError).code).toBe('NO_CONFIRMED_CLAIMS');
        expect((e as DraftError).statusCode).toBe(422);
      }
    });

    it('should throw NO_CONFIRMED_CLAIMS when claim set is empty', async () => {
      mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([]);

      await expect(
        DraftGenerationService.retrieveConfirmedClaims(validClaimSetId),
      ).rejects.toThrow(DraftError);

      try {
        mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce([]);
        await DraftGenerationService.retrieveConfirmedClaims(validClaimSetId);
      } catch (e) {
        expect((e as DraftError).code).toBe('NO_CONFIRMED_CLAIMS');
      }
    });
  });
});
