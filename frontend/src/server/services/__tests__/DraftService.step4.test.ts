/**
 * DraftService.step4.test.ts - Step 4: Generate draft text and claims_used metadata
 *
 * TLA+ Properties:
 * - Reachability: filtered claim set → { draft_text, claims_used }
 * - TypeInvariant: draft_text is string, claims_used is string[]
 * - ErrorConsistency: generation failure → GENERATION_FAILED
 *
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftService } from '../DraftService';
import { DraftError } from '@/server/error_definitions/DraftErrors';
import type { Claim, FilteredClaimSet } from '@/server/data_structures/DraftStoryRecord';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const confirmedHardClaim: Claim = {
  id: 'claim-1',
  text: 'Revenue increased by 30%',
  type: 'hard',
  truth_check: { status: 'confirmed', source: 'Q4 report' },
};

const softClaim: Claim = {
  id: 'claim-3',
  text: 'Team collaboration improved',
  type: 'soft',
};

const filteredClaims: FilteredClaimSet = [confirmedHardClaim, softClaim];

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftService.generateDraft — Step 4: Generate draft text and claims_used', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return draft_text and claims_used from filtered claims', () => {
      const result = DraftService.generateDraft(filteredClaims);

      expect(result).toBeDefined();
      expect(result.draft_text).toBeDefined();
      expect(result.claims_used).toBeDefined();
      expect(result.draft_text).toContain('Revenue increased by 30%');
      expect(result.draft_text).toContain('Team collaboration improved');
      expect(result.claims_used).toEqual(['claim-1', 'claim-3']);
    });

    it('should handle empty filtered claims gracefully', () => {
      const result = DraftService.generateDraft([]);

      expect(result.draft_text).toBe('');
      expect(result.claims_used).toEqual([]);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return draft_text as string', () => {
      const result = DraftService.generateDraft(filteredClaims);
      expect(typeof result.draft_text).toBe('string');
    });

    it('should return claims_used as string array of claim IDs', () => {
      const result = DraftService.generateDraft(filteredClaims);

      expect(Array.isArray(result.claims_used)).toBe(true);
      result.claims_used.forEach((id) => {
        expect(typeof id).toBe('string');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw GENERATION_FAILED on unexpected error', () => {
      // Force an error by passing a claims array that causes .map to fail
      const badClaims = null as unknown as FilteredClaimSet;

      try {
        DraftService.generateDraft(badClaims);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('GENERATION_FAILED');
        expect((e as DraftError).retryable).toBe(true);
      }
    });
  });
});
