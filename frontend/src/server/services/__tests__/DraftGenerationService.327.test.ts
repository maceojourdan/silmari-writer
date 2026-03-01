/**
 * DraftGenerationService.327.test.ts — Step 3: Check for confirmed claims
 *
 * TLA+ Properties:
 * - Reachability: Mock DAO returning claims with all `confirmed=false` → expect NoConfirmedClaimsError
 * - TypeInvariant: DAO returns StoryRecordClaim[] (with `confirmed: boolean`) → service processes typed array
 * - ErrorConsistency:
 *   - DAO throws → expect DataAccessError
 *   - No confirmed claims → expect NoConfirmedClaimsError
 *
 * Resource: db-h2s4 (service)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoryRecordClaimSchema } from '@/server/data_structures/Claim';
import type { StoryRecordClaim } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// Mock the ClaimDAO
vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getClaimsByStoryRecordId: vi.fn(),
    getClaimsByCaseId: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    getUnverifiedClaimsBySession: vi.fn(),
    updateStatusToVerified: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

// Mock StoryDAO (used by existing path 325 methods in same service)
vi.mock('@/server/data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    getClaimsBySetId: vi.fn(),
    saveDraft: vi.fn(),
  },
}));

// Mock the backend logger
vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { DraftGenerationService } from '../DraftGenerationService';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validStoryRecordId = 'story-record-abc-123';

function createStoryRecordClaim(overrides: Partial<StoryRecordClaim> = {}): StoryRecordClaim {
  return {
    id: `claim-${Math.random().toString(36).slice(2, 8)}`,
    storyRecordId: validStoryRecordId,
    confirmed: false,
    content: 'A test claim',
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerationService — Step 3: Check for confirmed claims (path 327)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should throw NO_CONFIRMED_CLAIMS when all claims have confirmed=false', async () => {
      const claims: StoryRecordClaim[] = [
        createStoryRecordClaim({ confirmed: false }),
        createStoryRecordClaim({ confirmed: false }),
        createStoryRecordClaim({ confirmed: false }),
      ];

      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(claims);

      await expect(
        DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId),
      ).rejects.toThrow(DraftError);

      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(claims);
      try {
        await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).code).toBe('NO_CONFIRMED_CLAIMS');
      }
    });

    it('should pass storyRecordId to the DAO', async () => {
      const confirmedClaim = createStoryRecordClaim({ confirmed: true });
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([confirmedClaim]);

      await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);

      expect(mockClaimDAO.getClaimsByStoryRecordId).toHaveBeenCalledWith(validStoryRecordId);
    });

    it('should return confirmed claims when at least one exists', async () => {
      const confirmedClaim = createStoryRecordClaim({ confirmed: true, content: 'Confirmed claim' });
      const unconfirmedClaim = createStoryRecordClaim({ confirmed: false, content: 'Unconfirmed claim' });

      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([confirmedClaim, unconfirmedClaim]);

      const result = await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);

      expect(result).toHaveLength(1);
      expect(result[0].confirmed).toBe(true);
      expect(result[0].content).toBe('Confirmed claim');
    });

    it('should throw NO_CONFIRMED_CLAIMS when claim list is empty', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([]);

      await expect(
        DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId),
      ).rejects.toThrow(DraftError);

      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([]);
      try {
        await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).code).toBe('NO_CONFIRMED_CLAIMS');
      }
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return array conforming to StoryRecordClaim schema', async () => {
      const confirmedClaim = createStoryRecordClaim({ confirmed: true });
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([confirmedClaim]);

      const result = await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);

      result.forEach((claim) => {
        const parsed = StoryRecordClaimSchema.safeParse(claim);
        expect(parsed.success).toBe(true);
      });
    });

    it('should preserve all StoryRecordClaim fields in the output', async () => {
      const confirmedClaim = createStoryRecordClaim({
        id: 'claim-specific-id',
        storyRecordId: validStoryRecordId,
        confirmed: true,
        content: 'Specific content',
      });
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([confirmedClaim]);

      const result = await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);

      expect(result[0]).toMatchObject({
        id: 'claim-specific-id',
        storyRecordId: validStoryRecordId,
        confirmed: true,
        content: 'Specific content',
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw DATA_ACCESS_ERROR when DAO throws', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockRejectedValueOnce(
        new Error('Database connection failed'),
      );

      await expect(
        DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId),
      ).rejects.toThrow(DraftError);

      mockClaimDAO.getClaimsByStoryRecordId.mockRejectedValueOnce(
        new Error('Database connection failed'),
      );
      try {
        await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).code).toBe('DATA_ACCESS_ERROR');
        expect((e as DraftError).statusCode).toBe(500);
      }
    });

    it('should throw NO_CONFIRMED_CLAIMS with 400 status when no confirmed claims', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([
        createStoryRecordClaim({ confirmed: false }),
      ]);

      try {
        await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).code).toBe('NO_CONFIRMED_CLAIMS');
        expect((e as DraftError).statusCode).toBe(400);
        expect((e as DraftError).message).toContain('No confirmed claims');
      }
    });

    it('should include storyRecordId in error message for DATA_ACCESS_ERROR', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockRejectedValueOnce(
        new Error('timeout'),
      );

      try {
        await DraftGenerationService.checkConfirmedClaimsForStoryRecord(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).message).toContain(validStoryRecordId);
      }
    });
  });
});
