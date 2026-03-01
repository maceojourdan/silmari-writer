/**
 * Tests for ObjectSchemaVerifier
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Provides cross-layer structural validation of session objects using Zod schemas.
 * This is the shared verifier that can be used at any layer boundary.
 *
 * TLA+ properties tested:
 * - Reachability: validate(validObjects) → { valid: true }
 * - TypeInvariant: result is always VerificationResult (VerificationSuccess | VerificationFailure)
 * - ErrorConsistency: invalid structure → { valid: false, errors: [...] } with object-level details
 */

import { describe, it, expect } from 'vitest';
import type { ResumeObject, JobObject, QuestionObject } from '../../data_structures/SessionObjects';

import { ObjectSchemaVerifier } from '../ObjectSchemaVerifier';
import type { VerificationResult } from '../ObjectSchemaVerifier';

describe('ObjectSchemaVerifier — Path 312: Structural validation of session objects', () => {
  const validResume: ResumeObject = {
    content: 'Experienced software engineer with 10 years of expertise in TypeScript.',
    name: 'John Doe Resume',
    wordCount: 10,
  };

  const validJob: JobObject = {
    title: 'Senior Software Engineer',
    description: 'We are looking for a senior engineer to lead our TypeScript team.',
    sourceType: 'text',
    sourceValue: 'We are looking for a senior engineer to lead our TypeScript team.',
  };

  const validQuestion: QuestionObject = {
    text: 'Tell me about a time you led a complex technical project.',
  };

  describe('Reachability: validate(validObjects) → { valid: true }', () => {
    it('should return valid: true for structurally valid objects', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      expect(result.valid).toBe(true);
    });

    it('should accept objects with optional fields populated', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: { ...validResume, id: '550e8400-e29b-41d4-a716-446655440000', createdAt: '2026-01-01' },
        job: { ...validJob, id: '660e8400-e29b-41d4-a716-446655440000', createdAt: '2026-01-01' },
        question: { ...validQuestion, id: '770e8400-e29b-41d4-a716-446655440000', category: 'behavioral', createdAt: '2026-01-01' },
      });

      expect(result.valid).toBe(true);
    });
  });

  describe('TypeInvariant: result is always VerificationResult', () => {
    it('should return VerificationSuccess shape for valid input', () => {
      const result: VerificationResult = ObjectSchemaVerifier.validate({
        resume: validResume,
        job: validJob,
        question: validQuestion,
      });

      expect(result).toHaveProperty('valid');
      expect(result.valid).toBe(true);
    });

    it('should return VerificationFailure shape with errors array for invalid input', () => {
      const result: VerificationResult = ObjectSchemaVerifier.validate({
        resume: { content: '', name: '', wordCount: -1 },
        job: validJob,
        question: validQuestion,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(Array.isArray(result.errors)).toBe(true);
        expect(result.errors.length).toBeGreaterThan(0);
      }
    });
  });

  describe('ErrorConsistency: invalid structure → { valid: false, errors: [...] } with object-level details', () => {
    it('should report errors for empty resume content', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: { content: '', name: 'Test', wordCount: 0 },
        job: validJob,
        question: validQuestion,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('resume'))).toBe(true);
      }
    });

    it('should report errors for empty job title', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: validResume,
        job: { ...validJob, title: '' },
        question: validQuestion,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('job'))).toBe(true);
      }
    });

    it('should report errors for empty question text', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: validResume,
        job: validJob,
        question: { text: '' },
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('question'))).toBe(true);
      }
    });

    it('should report errors for invalid job sourceType', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: validResume,
        job: { ...validJob, sourceType: 'invalid' as any },
        question: validQuestion,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('job'))).toBe(true);
      }
    });

    it('should aggregate errors from multiple invalid objects', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: { content: '', name: '', wordCount: -1 },
        job: { ...validJob, title: '' },
        question: { text: '' },
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('resume'))).toBe(true);
        expect(result.errors.some((e) => e.includes('job'))).toBe(true);
        expect(result.errors.some((e) => e.includes('question'))).toBe(true);
      }
    });

    it('should report negative wordCount as error', () => {
      const result = ObjectSchemaVerifier.validate({
        resume: { ...validResume, wordCount: -5 },
        job: validJob,
        question: validQuestion,
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some((e) => e.includes('resume'))).toBe(true);
      }
    });
  });
});
