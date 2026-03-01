/**
 * DraftGenerationService.compose.test.ts — Step 5: Generate structured draft from confirmed claims
 *
 * TLA+ Properties:
 * - Reachability: Input confirmed claims → output draft contains all claim texts
 * - TypeInvariant: Draft matches CaseDraft { caseId: string; content: string; claimsUsed: string[] }
 * - ErrorConsistency: Claim missing required `text` → DraftErrors326.GenerationError
 *
 * Resource: db-h2s4 (service)
 * Path: 326-generate-draft-with-only-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { CaseDraftSchema } from '@/server/data_structures/Claim';
import type { CaseClaim } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// Mock the ClaimDAO (required for DraftGenerationService import)
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

// Also mock StoryDAO (used by existing path 325 methods in same service)
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

describe('DraftGenerationService — Step 5: Compose draft from confirmed claims (path 326)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should produce draft containing all confirmed claim texts', () => {
      const claims: CaseClaim[] = [
        createCaseClaim({ id: 'c1', text: 'First confirmed claim' }),
        createCaseClaim({ id: 'c2', text: 'Second confirmed claim' }),
      ];

      const draft = DraftGenerationService.composeCaseDraft(validCaseId, claims);

      expect(draft.content).toContain('First confirmed claim');
      expect(draft.content).toContain('Second confirmed claim');
    });

    it('should join claim texts with double newlines', () => {
      const claims: CaseClaim[] = [
        createCaseClaim({ id: 'c1', text: 'Claim A' }),
        createCaseClaim({ id: 'c2', text: 'Claim B' }),
        createCaseClaim({ id: 'c3', text: 'Claim C' }),
      ];

      const draft = DraftGenerationService.composeCaseDraft(validCaseId, claims);

      expect(draft.content).toBe('Claim A\n\nClaim B\n\nClaim C');
    });

    it('should include all claim IDs in claimsUsed', () => {
      const claims: CaseClaim[] = [
        createCaseClaim({ id: 'c1' }),
        createCaseClaim({ id: 'c2' }),
        createCaseClaim({ id: 'c3' }),
      ];

      const draft = DraftGenerationService.composeCaseDraft(validCaseId, claims);

      expect(draft.claimsUsed).toEqual(['c1', 'c2', 'c3']);
    });

    it('should set caseId on the draft', () => {
      const claims: CaseClaim[] = [createCaseClaim({ id: 'c1' })];

      const draft = DraftGenerationService.composeCaseDraft(validCaseId, claims);

      expect(draft.caseId).toBe(validCaseId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return draft matching CaseDraft schema', () => {
      const claims: CaseClaim[] = [
        createCaseClaim({ id: 'c1', text: 'Test claim' }),
      ];

      const draft = DraftGenerationService.composeCaseDraft(validCaseId, claims);

      const parsed = CaseDraftSchema.safeParse(draft);
      expect(parsed.success).toBe(true);
    });

    it('should return object with exactly caseId, content, and claimsUsed fields', () => {
      const claims: CaseClaim[] = [createCaseClaim({ id: 'c1' })];

      const draft = DraftGenerationService.composeCaseDraft(validCaseId, claims);

      expect(Object.keys(draft).sort()).toEqual(['caseId', 'claimsUsed', 'content']);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw GENERATION_FAILED when claim has empty text', () => {
      const claims = [
        createCaseClaim({ id: 'c1', text: '' }),
      ] as unknown as CaseClaim[];

      expect(() =>
        DraftGenerationService.composeCaseDraft(validCaseId, claims),
      ).toThrow(DraftError);

      try {
        DraftGenerationService.composeCaseDraft(
          validCaseId,
          claims,
        );
      } catch (e) {
        expect((e as DraftError).code).toBe('GENERATION_FAILED');
      }
    });

    it('should throw GENERATION_FAILED when claims array is empty', () => {
      expect(() =>
        DraftGenerationService.composeCaseDraft(validCaseId, []),
      ).toThrow(DraftError);

      try {
        DraftGenerationService.composeCaseDraft(validCaseId, []);
      } catch (e) {
        expect((e as DraftError).code).toBe('GENERATION_FAILED');
      }
    });
  });
});
