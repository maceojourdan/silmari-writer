/**
 * answerUpdateVerifier.test.ts - Validate client-side edit submission
 *
 * TLA+ Properties:
 * - Reachability: validateAnswerUpdate(validId, validContent) → { valid: true, payload }
 * - TypeInvariant: valid result has payload { id: string; content: string }; invalid has errors: string[]
 * - ErrorConsistency: empty id → ['Answer ID is required']; empty content → ['Content is required']
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 337-prevent-edit-of-locked-answer
 */

import { describe, it, expect } from 'vitest';
import {
  validateAnswerUpdate,
  type UpdateAnswerPayload,
  type AnswerUpdateValidationResult,
} from '../answerUpdateVerifier';

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('answerUpdateVerifier — Validate edit submission (Path 337)', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return valid: true with payload for valid id and content', () => {
      const result = validateAnswerUpdate('abc-123', 'Updated answer');

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.payload).toEqual({
          id: 'abc-123',
          content: 'Updated answer',
        });
      }
    });

    it('should trim whitespace from id and content in payload', () => {
      const result = validateAnswerUpdate('  abc  ', '  hello  ');

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.payload).toEqual({
          id: 'abc',
          content: 'hello',
        });
      }
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return payload matching UpdateAnswerPayload { id: string; content: string }', () => {
      const result = validateAnswerUpdate('test-id', 'Some content');

      expect(result.valid).toBe(true);
      if (result.valid) {
        const payload: UpdateAnswerPayload = result.payload;
        expect(typeof payload.id).toBe('string');
        expect(typeof payload.content).toBe('string');
      }
    });

    it('should return errors as string array on invalid input', () => {
      const result = validateAnswerUpdate('', '');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(Array.isArray(result.errors)).toBe(true);
        result.errors.forEach((err) => {
          expect(typeof err).toBe('string');
        });
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should reject empty id with error message', () => {
      const result = validateAnswerUpdate('', 'Valid content');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toEqual(['Answer ID is required']);
      }
    });

    it('should reject empty content with error message', () => {
      const result = validateAnswerUpdate('valid-id', '');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toEqual(['Content is required']);
      }
    });

    it('should reject both empty id and content with both error messages', () => {
      const result = validateAnswerUpdate('', '');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toEqual([
          'Answer ID is required',
          'Content is required',
        ]);
      }
    });

    it('should reject whitespace-only id', () => {
      const result = validateAnswerUpdate('   ', 'Valid content');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toEqual(['Answer ID is required']);
      }
    });

    it('should reject whitespace-only content', () => {
      const result = validateAnswerUpdate('valid-id', '   ');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toEqual(['Content is required']);
      }
    });
  });
});
