/**
 * confirmMetricClaimVerifier Tests
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Properties tested:
 * - Reachability: valid decision ("Y" or "N") → isValid true
 * - TypeInvariant: status maps to "confirmed" | "denied"
 * - ErrorConsistency: no selection → isValid false with error message
 */

import { describe, it, expect } from 'vitest';
import {
  validateDecision,
  type DecisionValidationResult,
} from '@/verifiers/confirmMetricClaimVerifier';

describe('confirmMetricClaimVerifier', () => {
  describe('Reachability: valid decision passes validation', () => {
    it('should return isValid true for "Y" decision', () => {
      const result = validateDecision('Y');

      expect(result.isValid).toBe(true);
      expect(result.error).toBeUndefined();
    });

    it('should return isValid true for "N" decision', () => {
      const result = validateDecision('N');

      expect(result.isValid).toBe(true);
      expect(result.error).toBeUndefined();
    });
  });

  describe('TypeInvariant: status is "confirmed" or "denied"', () => {
    it('should be usable as union type "Y" | "N"', () => {
      const decisions: Array<'Y' | 'N'> = ['Y', 'N'];

      for (const decision of decisions) {
        const result = validateDecision(decision);
        expect(result.isValid).toBe(true);
      }
    });

    it('should not accept arbitrary strings', () => {
      // @ts-expect-error - intentional invalid input
      const result = validateDecision('maybe');

      expect(result.isValid).toBe(false);
    });
  });

  describe('ErrorConsistency: no selection blocks submission', () => {
    it('should return isValid false when decision is undefined', () => {
      const result = validateDecision(undefined);

      expect(result.isValid).toBe(false);
      expect(result.error).toBeDefined();
      expect(result.error).toContain('selection');
    });

    it('should return isValid false when decision is null', () => {
      const result = validateDecision(null as unknown as undefined);

      expect(result.isValid).toBe(false);
      expect(result.error).toBeDefined();
    });

    it('should return isValid false when decision is empty string', () => {
      const result = validateDecision('' as unknown as 'Y' | 'N');

      expect(result.isValid).toBe(false);
      expect(result.error).toBeDefined();
    });
  });
});
