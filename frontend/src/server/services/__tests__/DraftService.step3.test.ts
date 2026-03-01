/**
 * DraftService.step3.test.ts - Step 3: Filter unconfirmed hard claims
 *
 * TLA+ Properties:
 * - Reachability: StoryRecord with mixed claims → only confirmed hard + allowed claims
 * - TypeInvariant: output is FilteredClaimSet (Claim[])
 * - ErrorConsistency: missing metadata → excluded; invalid structure → INVALID_TRUTH_CHECK
 *
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftService } from '../DraftService';
import { DraftError } from '@/server/error_definitions/DraftErrors';
import type {
  DraftStoryRecord,
  Claim,
} from '@/server/data_structures/DraftStoryRecord';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const confirmedHardClaim: Claim = {
  id: 'claim-1',
  text: 'Revenue increased by 30%',
  type: 'hard',
  truth_check: { status: 'confirmed', source: 'Q4 report' },
};

const unconfirmedHardClaim: Claim = {
  id: 'claim-2',
  text: 'Cost reduced by 50%',
  type: 'hard',
  truth_check: { status: 'denied', source: 'audit' },
};

const softClaim: Claim = {
  id: 'claim-3',
  text: 'Team collaboration improved',
  type: 'soft',
};

const hardClaimMissingMetadata: Claim = {
  id: 'claim-4',
  text: 'Efficiency doubled',
  type: 'hard',
  // No truth_check at all — missing confirmation metadata
};

const recordWithMixedClaims: DraftStoryRecord = {
  id: 'record-001',
  status: 'DRAFT',
  truth_checks: [
    confirmedHardClaim,
    unconfirmedHardClaim,
    softClaim,
    hardClaimMissingMetadata,
  ],
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftService.filterConfirmedClaims — Step 3: Filter unconfirmed hard claims', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return only confirmed hard claims and soft claims', () => {
      const result = DraftService.filterConfirmedClaims(recordWithMixedClaims);

      expect(result).toHaveLength(2);

      const ids = result.map((c) => c.id);
      expect(ids).toContain('claim-1'); // confirmed hard
      expect(ids).toContain('claim-3'); // soft
      expect(ids).not.toContain('claim-2'); // denied hard → excluded
      expect(ids).not.toContain('claim-4'); // missing metadata hard → excluded
    });

    it('should include all soft claims regardless of truth_check', () => {
      const recordWithSoftOnly: DraftStoryRecord = {
        id: 'record-002',
        status: 'DRAFT',
        truth_checks: [softClaim],
      };

      const result = DraftService.filterConfirmedClaims(recordWithSoftOnly);
      expect(result).toHaveLength(1);
      expect(result[0].id).toBe('claim-3');
    });

    it('should return empty array when all hard claims are unconfirmed and no soft claims', () => {
      const recordAllUnconfirmed: DraftStoryRecord = {
        id: 'record-003',
        status: 'DRAFT',
        truth_checks: [unconfirmedHardClaim, hardClaimMissingMetadata],
      };

      const result = DraftService.filterConfirmedClaims(recordAllUnconfirmed);
      expect(result).toHaveLength(0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a FilteredClaimSet (Claim array)', () => {
      const result = DraftService.filterConfirmedClaims(recordWithMixedClaims);

      expect(Array.isArray(result)).toBe(true);
      result.forEach((claim) => {
        expect(claim).toHaveProperty('id');
        expect(claim).toHaveProperty('text');
        expect(claim).toHaveProperty('type');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should exclude hard claims with missing confirmation metadata (not throw)', () => {
      const result = DraftService.filterConfirmedClaims(recordWithMixedClaims);

      // claim-4 has no truth_check → excluded silently
      const ids = result.map((c) => c.id);
      expect(ids).not.toContain('claim-4');
    });

    it('should throw INVALID_TRUTH_CHECK for structurally invalid claims', () => {
      const recordWithBadStructure: DraftStoryRecord = {
        id: 'record-bad',
        status: 'DRAFT',
        truth_checks: [
          { id: '', text: '', type: 'hard' }, // empty id and text → Zod min(1) fails
        ],
      };

      try {
        DraftService.filterConfirmedClaims(recordWithBadStructure);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('INVALID_TRUTH_CHECK');
      }
    });
  });
});
