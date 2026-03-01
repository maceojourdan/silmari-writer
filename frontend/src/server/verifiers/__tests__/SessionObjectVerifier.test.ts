/**
 * Tests for SessionObjectVerifier
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: validate(validObjects) → { valid: true }
 * - TypeInvariant: returns typed VerificationResult
 * - ErrorConsistency: invalid objects → { valid: false, errors: [...] }
 */

import { describe, it, expect } from 'vitest';
import { SessionObjectVerifier } from '../SessionObjectVerifier';
import type { TransformedSessionInput } from '../../transformers/SessionInputTransformer';

describe('SessionObjectVerifier', () => {
  const validObjects: TransformedSessionInput = {
    resume: {
      content: 'Experienced software engineer...',
      name: 'Uploaded Resume',
      wordCount: 3,
    },
    job: {
      title: 'Senior Developer',
      description: 'Job description text...',
      sourceType: 'text',
      sourceValue: 'Job description text...',
    },
    question: {
      text: 'Tell me about a challenge.',
    },
  };

  describe('Reachability: valid objects → valid: true', () => {
    it('should return valid: true for well-formed objects', () => {
      const result = SessionObjectVerifier.validate(validObjects);
      expect(result.valid).toBe(true);
    });
  });

  describe('ErrorConsistency: invalid objects → valid: false with errors', () => {
    it('should fail when resume content is empty', () => {
      const invalid: TransformedSessionInput = {
        ...validObjects,
        resume: { ...validObjects.resume, content: '' },
      };

      const result = SessionObjectVerifier.validate(invalid);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('resume'))).toBe(true);
      }
    });

    it('should fail when job title is empty', () => {
      const invalid: TransformedSessionInput = {
        ...validObjects,
        job: { ...validObjects.job, title: '' },
      };

      const result = SessionObjectVerifier.validate(invalid);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('job'))).toBe(true);
      }
    });

    it('should fail when question text is empty', () => {
      const invalid: TransformedSessionInput = {
        ...validObjects,
        question: { text: '' },
      };

      const result = SessionObjectVerifier.validate(invalid);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('question'))).toBe(true);
      }
    });

    it('should fail when resume wordCount is negative', () => {
      const invalid: TransformedSessionInput = {
        ...validObjects,
        resume: { ...validObjects.resume, wordCount: -1 },
      };

      const result = SessionObjectVerifier.validate(invalid);
      expect(result.valid).toBe(false);
    });

    it('should collect errors from multiple invalid objects', () => {
      const invalid: TransformedSessionInput = {
        resume: { content: '', name: '', wordCount: -1 },
        job: { title: '', description: '', sourceType: 'text', sourceValue: '' },
        question: { text: '' },
      };

      const result = SessionObjectVerifier.validate(invalid);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.length).toBeGreaterThan(2);
      }
    });
  });
});
