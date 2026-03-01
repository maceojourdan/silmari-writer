/**
 * Tests for SessionInitVerifier
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: validateSessionInitInput(validInput) → { success: true }
 * - TypeInvariant: parsed result matches InitSessionRequestSchema (Zod)
 * - ErrorConsistency: missing resume → { success: false, errors: { resume: ... } }
 */

import { describe, it, expect } from 'vitest';
import {
  validateSessionInitInput,
  type SessionInitInput,
} from '../SessionInitVerifier';

describe('SessionInitVerifier', () => {
  const validInput: SessionInitInput = {
    resume: 'Experienced software engineer with 10 years of expertise in distributed systems...',
    jobText: 'Senior Software Engineer at Acme Corp. Must have experience with distributed systems and cloud infrastructure.',
    questionText: 'Tell me about a time you led a complex technical project.',
  };

  describe('Reachability: valid input produces success result', () => {
    it('should return success: true for valid input with all required fields', () => {
      const result = validateSessionInitInput(validInput);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data.resume).toBe(validInput.resume);
        expect(result.data.jobText).toBe(validInput.jobText);
        expect(result.data.questionText).toBe(validInput.questionText);
      }
    });

    it('should accept input with optional jobLink instead of jobText', () => {
      const inputWithLink: SessionInitInput = {
        resume: 'My resume content...',
        jobLink: 'https://example.com/job/123',
        questionText: 'What is your greatest strength?',
      };

      const result = validateSessionInitInput(inputWithLink);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data.jobLink).toBe('https://example.com/job/123');
      }
    });

    it('should accept input with both jobLink and jobText', () => {
      const inputWithBoth: SessionInitInput = {
        resume: 'My resume content...',
        jobLink: 'https://example.com/job/123',
        jobText: 'Senior Developer position',
        questionText: 'Describe a challenge you overcame.',
      };

      const result = validateSessionInitInput(inputWithBoth);
      expect(result.success).toBe(true);
    });
  });

  describe('TypeInvariant: parsed result matches schema', () => {
    it('should return data with correct types', () => {
      const result = validateSessionInitInput(validInput);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(typeof result.data.resume).toBe('string');
        expect(typeof result.data.questionText).toBe('string');
        // jobText or jobLink should be string
        expect(
          typeof result.data.jobText === 'string' ||
          typeof result.data.jobLink === 'string',
        ).toBe(true);
      }
    });
  });

  describe('ErrorConsistency: missing/invalid fields produce structured errors', () => {
    it('should fail when resume is missing', () => {
      const result = validateSessionInitInput({
        jobText: 'Some job description',
        questionText: 'Some question',
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.some((e) => e.includes('resume'))).toBe(true);
      }
    });

    it('should fail when resume is empty string', () => {
      const result = validateSessionInitInput({
        resume: '',
        jobText: 'Some job description',
        questionText: 'Some question',
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.some((e) => e.includes('resume'))).toBe(true);
      }
    });

    it('should fail when questionText is missing', () => {
      const result = validateSessionInitInput({
        resume: 'My resume...',
        jobText: 'Some job description',
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.some((e) => e.includes('questionText'))).toBe(true);
      }
    });

    it('should fail when neither jobText nor jobLink is provided', () => {
      const result = validateSessionInitInput({
        resume: 'My resume...',
        questionText: 'Some question',
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(
          result.errors.some((e) => e.toLowerCase().includes('job')),
        ).toBe(true);
      }
    });

    it('should fail when jobLink is not a valid URL', () => {
      const result = validateSessionInitInput({
        resume: 'My resume...',
        jobLink: 'not-a-url',
        questionText: 'Some question',
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.some((e) => e.includes('jobLink'))).toBe(true);
      }
    });

    it('should fail when all fields are missing', () => {
      const result = validateSessionInitInput({});

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBeGreaterThan(0);
      }
    });

    it('should fail for non-object input', () => {
      const result = validateSessionInitInput(null);

      expect(result.success).toBe(false);
    });
  });
});
