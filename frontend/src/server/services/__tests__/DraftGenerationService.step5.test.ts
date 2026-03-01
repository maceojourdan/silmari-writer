/**
 * DraftGenerationService.step5.test.ts - Step 5: Persist and return generated draft
 *
 * TLA+ Properties:
 * - Reachability: Mock DAO saveDraft() success → draft persisted and returned
 * - TypeInvariant: Saved draft matches StructuredDraft schema
 * - ErrorConsistency: DB error → throw DraftErrors.PERSISTENCE_FAILED
 *
 * Resource: db-h2s4 (service)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  StructuredDraftSchema,
  type StructuredDraft,
  type StoryClaim,
} from '@/server/data_structures/StoryStructures';
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

function createValidDraft(): StructuredDraft {
  return {
    id: crypto.randomUUID(),
    claimSetId: validClaimSetId,
    sections: [
      {
        sectionName: 'context',
        claims: [createClaim({ section: 'context', order: 0 })],
      },
      {
        sectionName: 'actions',
        claims: [createClaim({ section: 'actions', order: 0 })],
      },
      {
        sectionName: 'outcome',
        claims: [createClaim({ section: 'outcome', order: 0 })],
      },
    ],
    createdAt: now,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerationService.persistDraft — Step 5', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should persist draft via DAO and return saved draft', async () => {
      const draft = createValidDraft();
      mockStoryDAO.saveDraft.mockResolvedValueOnce(draft);

      const result = await DraftGenerationService.persistDraft(draft);

      expect(mockStoryDAO.saveDraft).toHaveBeenCalledWith(draft);
      expect(result).toEqual(draft);
    });

    it('should pass the complete draft object to DAO', async () => {
      const draft = createValidDraft();
      mockStoryDAO.saveDraft.mockResolvedValueOnce(draft);

      await DraftGenerationService.persistDraft(draft);

      const passedDraft = mockStoryDAO.saveDraft.mock.calls[0][0];
      expect(passedDraft.id).toBe(draft.id);
      expect(passedDraft.claimSetId).toBe(draft.claimSetId);
      expect(passedDraft.sections).toEqual(draft.sections);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result conforming to StructuredDraft schema', async () => {
      const draft = createValidDraft();
      mockStoryDAO.saveDraft.mockResolvedValueOnce(draft);

      const result = await DraftGenerationService.persistDraft(draft);

      const parsed = StructuredDraftSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw PERSISTENCE_FAILED when DAO throws', async () => {
      const draft = createValidDraft();
      mockStoryDAO.saveDraft.mockRejectedValueOnce(new Error('DB connection lost'));

      await expect(
        DraftGenerationService.persistDraft(draft),
      ).rejects.toThrow(DraftError);

      try {
        mockStoryDAO.saveDraft.mockRejectedValueOnce(new Error('DB connection lost'));
        await DraftGenerationService.persistDraft(draft);
      } catch (e) {
        expect((e as DraftError).code).toBe('PERSISTENCE_FAILED');
        expect((e as DraftError).statusCode).toBe(500);
        expect((e as DraftError).retryable).toBe(true);
      }
    });

    it('should include original error message in wrapped error', async () => {
      const draft = createValidDraft();
      mockStoryDAO.saveDraft.mockRejectedValueOnce(new Error('disk full'));

      try {
        await DraftGenerationService.persistDraft(draft);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as DraftError).message).toContain('disk full');
      }
    });
  });
});

// ---------------------------------------------------------------------------
// Full generate() orchestration test
// ---------------------------------------------------------------------------

describe('DraftGenerationService.generate — Full orchestration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should retrieve → transform → persist and return the draft', async () => {
    // Setup: claim set with claims in all required sections
    const claims: StoryClaim[] = [
      createClaim({ section: 'context', order: 0, content: 'Context' }),
      createClaim({ section: 'actions', order: 0, content: 'Actions' }),
      createClaim({ section: 'outcome', order: 0, content: 'Outcome' }),
      createClaim({ section: 'context', order: 1, status: 'UNCONFIRMED', content: 'Filtered out' }),
    ];

    mockStoryDAO.getClaimsBySetId.mockResolvedValueOnce(claims);
    mockStoryDAO.saveDraft.mockImplementationOnce(async (draft) => draft);

    const result = await DraftGenerationService.generate(validClaimSetId);

    // Verify full flow
    expect(mockStoryDAO.getClaimsBySetId).toHaveBeenCalledWith(validClaimSetId);
    expect(mockStoryDAO.saveDraft).toHaveBeenCalledTimes(1);

    // Verify result structure
    expect(result.claimSetId).toBe(validClaimSetId);
    expect(result.sections).toHaveLength(3);

    // Verify only confirmed claims in output
    const allClaims = result.sections.flatMap((s) => s.claims);
    expect(allClaims.every((c) => c.status === 'CONFIRMED')).toBe(true);
    expect(allClaims).toHaveLength(3); // Unconfirmed one filtered out
  });
});
