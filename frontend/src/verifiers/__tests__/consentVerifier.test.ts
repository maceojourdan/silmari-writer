/**
 * Tests for consentVerifier
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * TLA+ properties tested:
 * - Reachability: "I agree" → returns true
 * - TypeInvariant: consentFlag is boolean
 * - ErrorConsistency: "No" → returns false; undefined → returns false
 */

import { describe, it, expect } from 'vitest';
import { isExplicitlyAffirmative } from '../consentVerifier';

describe('consentVerifier', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return true for "I agree"', () => {
      expect(isExplicitlyAffirmative('I agree')).toBe(true);
    });

    it('should return true for "yes"', () => {
      expect(isExplicitlyAffirmative('yes')).toBe(true);
    });

    it('should return true for "I AGREE" (case insensitive)', () => {
      expect(isExplicitlyAffirmative('I AGREE')).toBe(true);
    });

    it('should return true for "Yes" (case insensitive)', () => {
      expect(isExplicitlyAffirmative('Yes')).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should always return a boolean value', () => {
      const trueResult = isExplicitlyAffirmative('yes');
      const falseResult = isExplicitlyAffirmative('no');

      expect(typeof trueResult).toBe('boolean');
      expect(typeof falseResult).toBe('boolean');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return false for "No"', () => {
      expect(isExplicitlyAffirmative('No')).toBe(false);
    });

    it('should return false for "decline"', () => {
      expect(isExplicitlyAffirmative('decline')).toBe(false);
    });

    it('should return false for empty string', () => {
      expect(isExplicitlyAffirmative('')).toBe(false);
    });

    it('should return false for undefined input', () => {
      expect(isExplicitlyAffirmative(undefined as unknown as string)).toBe(false);
    });

    it('should return false for null input', () => {
      expect(isExplicitlyAffirmative(null as unknown as string)).toBe(false);
    });

    it('should return false for arbitrary text', () => {
      expect(isExplicitlyAffirmative('maybe')).toBe(false);
    });

    it('should return false for numeric input', () => {
      expect(isExplicitlyAffirmative(123 as unknown as string)).toBe(false);
    });
  });
});
