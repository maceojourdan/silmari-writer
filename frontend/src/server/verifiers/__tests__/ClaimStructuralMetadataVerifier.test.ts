/**
 * ClaimStructuralMetadataVerifier.test.ts — Step 3: Validate structural metadata completeness
 *
 * TLA+ Properties:
 * - Reachability: Given claims with/without required fields → correctly partitioned
 * - TypeInvariant: Both arrays contain correct types
 * - ErrorConsistency: Simulate rule evaluation failure → claim appears in incomplete set; logger called
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 328-exclude-incomplete-claim-during-draft-generation
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { ConfirmedClaim, IncompleteClaimReport } from '@/server/data_structures/Claim';
import { ConfirmedClaimSchema, IncompleteClaimReportSchema } from '@/server/data_structures/Claim';

// Mock logger
vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { logger } from '@/server/logging/logger';
import { ClaimStructuralMetadataVerifier } from '../ClaimStructuralMetadataVerifier';

const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'session-test-328-002';

function createCompleteClaim(overrides: Partial<ConfirmedClaim> = {}): ConfirmedClaim {
  return {
    id: `claim-${Math.random().toString(36).slice(2, 8)}`,
    sessionId: validSessionId,
    content: 'Increased revenue by 25% through strategic initiative',
    status: 'CONFIRMED',
    metric: '25% revenue increase',
    scope: 'Q3 2025 sales division',
    context: 'Strategic client outreach program',
    created_at: new Date().toISOString(),
    updated_at: new Date().toISOString(),
    ...overrides,
  };
}

function createIncompleteClaim(
  missingFieldOverrides: Partial<Pick<ConfirmedClaim, 'metric' | 'scope' | 'context'>> = {},
  overrides: Partial<ConfirmedClaim> = {},
): ConfirmedClaim {
  return {
    id: `claim-${Math.random().toString(36).slice(2, 8)}`,
    sessionId: validSessionId,
    content: 'Led a cross-functional team',
    status: 'CONFIRMED',
    metric: '25% increase',
    scope: 'Q3 sales',
    context: 'Outreach initiative',
    ...missingFieldOverrides,
    created_at: new Date().toISOString(),
    updated_at: new Date().toISOString(),
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ClaimStructuralMetadataVerifier — Step 3: Validate structural metadata completeness (path 328)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should put claims with all required fields into complete set', () => {
      const completeClaim = createCompleteClaim({ id: 'c1' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([completeClaim]);

      expect(result.complete).toHaveLength(1);
      expect(result.complete[0].id).toBe('c1');
      expect(result.incomplete).toHaveLength(0);
    });

    it('should put claims missing metric into incomplete set', () => {
      const claim = createIncompleteClaim({ metric: undefined }, { id: 'c2' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([claim]);

      expect(result.complete).toHaveLength(0);
      expect(result.incomplete).toHaveLength(1);
      expect(result.incomplete[0].claimId).toBe('c2');
      expect(result.incomplete[0].missingFields).toContain('metric');
    });

    it('should put claims missing scope into incomplete set', () => {
      const claim = createIncompleteClaim({ scope: undefined }, { id: 'c3' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([claim]);

      expect(result.complete).toHaveLength(0);
      expect(result.incomplete).toHaveLength(1);
      expect(result.incomplete[0].missingFields).toContain('scope');
    });

    it('should put claims missing context into incomplete set', () => {
      const claim = createIncompleteClaim({ context: undefined }, { id: 'c4' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([claim]);

      expect(result.complete).toHaveLength(0);
      expect(result.incomplete).toHaveLength(1);
      expect(result.incomplete[0].missingFields).toContain('context');
    });

    it('should correctly partition a mix of complete and incomplete claims', () => {
      const complete1 = createCompleteClaim({ id: 'complete-1' });
      const complete2 = createCompleteClaim({ id: 'complete-2' });
      const incomplete1 = createIncompleteClaim({ metric: undefined }, { id: 'incomplete-1' });
      const incomplete2 = createIncompleteClaim({ scope: undefined, context: undefined }, { id: 'incomplete-2' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([
        complete1,
        incomplete1,
        complete2,
        incomplete2,
      ]);

      expect(result.complete).toHaveLength(2);
      expect(result.complete.map((c) => c.id)).toEqual(['complete-1', 'complete-2']);
      expect(result.incomplete).toHaveLength(2);
      expect(result.incomplete.map((c) => c.claimId)).toEqual(['incomplete-1', 'incomplete-2']);
    });

    it('should report multiple missing fields when several are absent', () => {
      const claim = createIncompleteClaim(
        { metric: undefined, scope: undefined, context: undefined },
        { id: 'c5' },
      );

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([claim]);

      expect(result.incomplete[0].missingFields).toEqual(
        expect.arrayContaining(['metric', 'scope', 'context']),
      );
      expect(result.incomplete[0].missingFields).toHaveLength(3);
    });

    it('should treat empty string fields as missing', () => {
      const claim = createCompleteClaim({
        id: 'c6',
        metric: '',
        scope: '  ',
        context: 'Valid context',
      });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([claim]);

      expect(result.complete).toHaveLength(0);
      expect(result.incomplete).toHaveLength(1);
      expect(result.incomplete[0].missingFields).toContain('metric');
      expect(result.incomplete[0].missingFields).toContain('scope');
    });

    it('should return empty sets for empty input', () => {
      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([]);

      expect(result.complete).toEqual([]);
      expect(result.incomplete).toEqual([]);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return complete claims conforming to ConfirmedClaim schema', () => {
      const claim = createCompleteClaim({ id: 'c1' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([claim]);

      for (const c of result.complete) {
        const parsed = ConfirmedClaimSchema.safeParse(c);
        expect(parsed.success).toBe(true);
      }
    });

    it('should return incomplete reports conforming to IncompleteClaimReport schema', () => {
      const claim = createIncompleteClaim({ metric: undefined }, { id: 'c2' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([claim]);

      for (const report of result.incomplete) {
        const parsed = IncompleteClaimReportSchema.safeParse(report);
        expect(parsed.success).toBe(true);
      }
    });

    it('should include both complete and incomplete in the return value', () => {
      const complete = createCompleteClaim({ id: 'c1' });
      const incomplete = createIncompleteClaim({ metric: undefined }, { id: 'c2' });

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness([complete, incomplete]);

      expect(result).toHaveProperty('complete');
      expect(result).toHaveProperty('incomplete');
      expect(Array.isArray(result.complete)).toBe(true);
      expect(Array.isArray(result.incomplete)).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should treat claim as incomplete when rule evaluation throws and log the error', () => {
      // Create a claim with a getter that throws during field access
      const badClaim = {
        id: 'bad-claim',
        sessionId: validSessionId,
        content: 'Some content',
        status: 'CONFIRMED' as const,
        get metric(): string {
          throw new Error('Cannot read metric');
        },
        scope: 'Valid scope',
        context: 'Valid context',
        created_at: new Date().toISOString(),
        updated_at: new Date().toISOString(),
      };

      const result = ClaimStructuralMetadataVerifier.partitionByCompleteness(
        [badClaim] as ConfirmedClaim[],
      );

      expect(result.complete).toHaveLength(0);
      expect(result.incomplete).toHaveLength(1);
      expect(result.incomplete[0].claimId).toBe('bad-claim');
      expect(mockLogger.error).toHaveBeenCalledWith(
        'Rule evaluation failed for claim; treating as incomplete',
        expect.any(Error),
        expect.objectContaining({ path: '328', resource: 'db-j6x9', claimId: 'bad-claim' }),
      );
    });
  });
});
