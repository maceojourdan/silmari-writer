/**
 * DraftGenerationService.step4.test.ts - Step 4: Transform confirmed claims into structured draft
 *
 * TLA+ Properties:
 * - Reachability: Confirmed claims with valid structural metadata → output matches DraftDocumentStructure
 * - TypeInvariant: Output matches StructuredDraft schema from StoryStructures.ts
 * - ErrorConsistency: Missing required structural field → throw SharedErrors.TRANSFORMATION_ERROR
 *
 * Resource: db-h2s4 (service)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  StructuredDraftSchema,
  type StoryClaim,
} from '@/server/data_structures/StoryStructures';
import { DRAFT_SECTIONS } from '@/server/data_structures/DraftDocumentStructure';
import { SharedError } from '@/server/error_definitions/SharedErrors';

// Mock the StoryDAO (not used directly, but service imports it)
vi.mock('@/server/data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    getClaimsBySetId: vi.fn(),
    saveDraft: vi.fn(),
  },
}));

import { DraftGenerationService } from '../DraftGenerationService';

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

function createFullClaimSet(): StoryClaim[] {
  return [
    createClaim({ section: 'context', order: 0, content: 'Context claim 1' }),
    createClaim({ section: 'context', order: 1, content: 'Context claim 2' }),
    createClaim({ section: 'actions', order: 0, content: 'Actions claim 1' }),
    createClaim({ section: 'actions', order: 1, content: 'Actions claim 2' }),
    createClaim({ section: 'outcome', order: 0, content: 'Outcome claim 1' }),
  ];
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerationService.transformClaimsToDraft — Step 4', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should produce a structured draft with all required sections', () => {
      const claims = createFullClaimSet();

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      expect(draft.sections).toHaveLength(DRAFT_SECTIONS.length);
      expect(draft.sections.map((s) => s.sectionName)).toEqual([
        'context',
        'actions',
        'outcome',
      ]);
    });

    it('should group claims into correct sections', () => {
      const claims = createFullClaimSet();

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      const contextSection = draft.sections.find((s) => s.sectionName === 'context');
      const actionsSection = draft.sections.find((s) => s.sectionName === 'actions');
      const outcomeSection = draft.sections.find((s) => s.sectionName === 'outcome');

      expect(contextSection?.claims).toHaveLength(2);
      expect(actionsSection?.claims).toHaveLength(2);
      expect(outcomeSection?.claims).toHaveLength(1);
    });

    it('should order claims within sections by their order field', () => {
      const claims = [
        createClaim({ section: 'context', order: 2, content: 'Second' }),
        createClaim({ section: 'context', order: 0, content: 'First' }),
        createClaim({ section: 'context', order: 1, content: 'Middle' }),
        createClaim({ section: 'actions', order: 0, content: 'Action' }),
        createClaim({ section: 'outcome', order: 0, content: 'Outcome' }),
      ];

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      const contextSection = draft.sections.find((s) => s.sectionName === 'context');
      expect(contextSection?.claims.map((c) => c.content)).toEqual([
        'First',
        'Middle',
        'Second',
      ]);
    });

    it('should set the claimSetId on the draft', () => {
      const claims = createFullClaimSet();

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      expect(draft.claimSetId).toBe(validClaimSetId);
    });

    it('should generate a UUID for the draft id', () => {
      const claims = createFullClaimSet();

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      expect(draft.id).toBeDefined();
      expect(typeof draft.id).toBe('string');
      expect(draft.id.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should conform to StructuredDraft schema', () => {
      const claims = createFullClaimSet();

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      const parsed = StructuredDraftSchema.safeParse(draft);
      expect(parsed.success).toBe(true);
    });

    it('should have a valid createdAt timestamp', () => {
      const claims = createFullClaimSet();

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      expect(draft.createdAt).toBeDefined();
      expect(new Date(draft.createdAt).toISOString()).toBe(draft.createdAt);
    });

    it('should preserve claim structure within sections', () => {
      const claims = createFullClaimSet();

      const draft = DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);

      for (const section of draft.sections) {
        for (const claim of section.claims) {
          expect(claim).toHaveProperty('id');
          expect(claim).toHaveProperty('content');
          expect(claim).toHaveProperty('status');
          expect(claim).toHaveProperty('section');
          expect(claim).toHaveProperty('order');
        }
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw TRANSFORMATION_ERROR when a required section has no claims', () => {
      // Missing 'outcome' section
      const claims = [
        createClaim({ section: 'context', order: 0 }),
        createClaim({ section: 'actions', order: 0 }),
      ];

      expect(() =>
        DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims),
      ).toThrow(SharedError);

      try {
        DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);
      } catch (e) {
        expect((e as SharedError).code).toBe('TRANSFORMATION_ERROR');
        expect((e as SharedError).statusCode).toBe(422);
      }
    });

    it('should throw TRANSFORMATION_ERROR when missing multiple required sections', () => {
      // Only 'context' section provided
      const claims = [createClaim({ section: 'context', order: 0 })];

      expect(() =>
        DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims),
      ).toThrow(SharedError);

      try {
        DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);
      } catch (e) {
        expect((e as SharedError).code).toBe('TRANSFORMATION_ERROR');
        expect((e as SharedError).message).toContain('actions');
      }
    });

    it('should include missing section name in error message', () => {
      const claims = [
        createClaim({ section: 'context', order: 0 }),
        createClaim({ section: 'actions', order: 0 }),
        // Missing 'outcome'
      ];

      try {
        DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as SharedError).message).toContain('outcome');
      }
    });

    it('should throw TRANSFORMATION_ERROR when a claim has an invalid section name', () => {
      const claims = [
        createClaim({ section: 'context', order: 0 }),
        createClaim({ section: 'actions', order: 0 }),
        createClaim({ section: 'outcome', order: 0 }),
        // Claim with invalid section — cast to bypass TypeScript enum restriction
        createClaim({ section: 'bogus' as unknown as 'context', order: 0 }),
      ];

      expect(() =>
        DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims),
      ).toThrow(SharedError);

      try {
        DraftGenerationService.transformClaimsToDraft(validClaimSetId, claims);
      } catch (e) {
        expect((e as SharedError).code).toBe('TRANSFORMATION_ERROR');
        expect((e as SharedError).statusCode).toBe(422);
        expect((e as SharedError).message).toContain('bogus');
      }
    });
  });
});
