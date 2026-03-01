/**
 * Tests for SessionObjectVerifier.verifyPresence
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Performs backend-level semantic validation: checks that required domain
 * objects are present (not null/undefined) before structural validation.
 *
 * TLA+ properties tested:
 * - Reachability: verifyPresence(allPresent) → { valid: true }
 * - TypeInvariant: result is always VerificationResult
 * - ErrorConsistency: missing object → { valid: false, errors: [...] } identifying the missing object
 */

import { describe, it, expect } from 'vitest';
import type { ResumeObject, JobObject, QuestionObject } from '../../data_structures/SessionObjects';
import { SessionObjectVerifier } from '../SessionObjectVerifier';
import type { VerificationResult } from '../SessionObjectVerifier';

describe('SessionObjectVerifier.verifyPresence — Path 312: Presence validation', () => {
  const validResume: ResumeObject = {
    content: 'Experienced software engineer with expertise in TypeScript.',
    name: 'Test Resume',
    wordCount: 8,
  };

  const validJob: JobObject = {
    title: 'Senior Engineer',
    description: 'Lead engineering team.',
    sourceType: 'text',
    sourceValue: 'Lead engineering team.',
  };

  const validQuestion: QuestionObject = {
    text: 'Tell me about a time you led a complex project.',
  };

  describe('Reachability: verifyPresence(allPresent) → { valid: true }', () => {
    it('should return valid: true when all objects are present', () => {
      const result = SessionObjectVerifier.verifyPresence({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      expect(result.valid).toBe(true);
    });
  });

  describe('TypeInvariant: result is always VerificationResult', () => {
    it('should return VerificationSuccess for present objects', () => {
      const result: VerificationResult = SessionObjectVerifier.verifyPresence({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      expect(result).toHaveProperty('valid');
      expect(result.valid).toBe(true);
    });

    it('should return VerificationFailure for missing objects', () => {
      const result: VerificationResult = SessionObjectVerifier.verifyPresence({
        resume: undefined,
        job: validJob,
        question: validQuestion,
      });

      expect(result).toHaveProperty('valid');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result).toHaveProperty('errors');
        expect(Array.isArray(result.errors)).toBe(true);
      }
    });
  });

  describe('ErrorConsistency: missing object → errors identifying the missing object', () => {
    it('should report missing ResumeObject', () => {
      const result = SessionObjectVerifier.verifyPresence({
        resume: undefined,
        job: validJob,
        question: validQuestion,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('ResumeObject'))).toBe(true);
      }
    });

    it('should report missing JobObject', () => {
      const result = SessionObjectVerifier.verifyPresence({
        resume: validResume,
        job: undefined,
        question: validQuestion,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('JobObject'))).toBe(true);
      }
    });

    it('should report missing QuestionObject', () => {
      const result = SessionObjectVerifier.verifyPresence({
        resume: validResume,
        job: validJob,
        question: undefined,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('QuestionObject'))).toBe(true);
      }
    });

    it('should report null objects as missing', () => {
      const result = SessionObjectVerifier.verifyPresence({
        resume: null,
        job: null,
        question: null,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toHaveLength(3);
        expect(result.errors.some((e) => e.includes('ResumeObject'))).toBe(true);
        expect(result.errors.some((e) => e.includes('JobObject'))).toBe(true);
        expect(result.errors.some((e) => e.includes('QuestionObject'))).toBe(true);
      }
    });

    it('should report all missing objects when all are undefined', () => {
      const result = SessionObjectVerifier.verifyPresence({
        resume: undefined,
        job: undefined,
        question: undefined,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toHaveLength(3);
      }
    });
  });
});
