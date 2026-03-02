/**
 * VoiceInputVerifier.test.ts - Step 2: Collect and validate voice input
 *
 * TLA+ Properties:
 * - Reachability: validateVoiceInput(validTranscript, durationMs) → { valid: true, payload }
 * - TypeInvariant: payload matches VoicePayload { transcript: string; durationMs: number }
 * - ErrorConsistency: empty/unintelligible transcript → { valid: false, error: VOICE_INPUT_INVALID }
 *   + no backend API contract invoked
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 332-voice-edit-no-input-error-on-review-screen
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  validateVoiceInput,
  type VoicePayload,
  type VoiceInputValidationResult,
} from '../VoiceInputVerifier';
import { VoiceInputErrors } from '@/server/error_definitions/VoiceErrors';

const mockFetch = vi.fn();

describe('VoiceInputVerifier — Step 2: Validate voice input (Path 332)', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return valid: true with payload for valid transcript', () => {
      const result = validateVoiceInput('Make the introduction more concise', 3500);

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.payload).toBeDefined();
        expect(result.payload.transcript).toBe('Make the introduction more concise');
        expect(result.payload.durationMs).toBe(3500);
      }
    });

    it('should accept transcript with exactly 3 characters', () => {
      const result = validateVoiceInput('Fix', 1000);

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.payload.transcript).toBe('Fix');
      }
    });

    it('should trim transcript whitespace and still validate', () => {
      const result = validateVoiceInput('  Fix this paragraph  ', 2000);

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.payload.transcript).toBe('Fix this paragraph');
      }
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return payload matching VoicePayload type { transcript: string; durationMs: number }', () => {
      const result = validateVoiceInput('Rewrite the conclusion', 5000);

      expect(result.valid).toBe(true);
      if (result.valid) {
        const payload: VoicePayload = result.payload;
        expect(typeof payload.transcript).toBe('string');
        expect(typeof payload.durationMs).toBe('number');
      }
    });

    it('should return error object with code and message fields on failure', () => {
      const result = validateVoiceInput('', 0);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(typeof result.error.code).toBe('string');
        expect(typeof result.error.message).toBe('string');
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should reject empty transcript', () => {
      const result = validateVoiceInput('', 0);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toEqual(VoiceInputErrors.VOICE_INPUT_INVALID);
      }
    });

    it('should reject transcript below intelligibility threshold (< 3 chars)', () => {
      const result = validateVoiceInput('ab', 500);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error.code).toBe('VOICE_INPUT_INVALID');
      }
    });

    it('should reject whitespace-only transcript', () => {
      const result = validateVoiceInput('   ', 1000);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toEqual(VoiceInputErrors.VOICE_INPUT_INVALID);
      }
    });

    it('should reject transcript with only 2 chars after trimming', () => {
      const result = validateVoiceInput('  ab  ', 800);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error.code).toBe('VOICE_INPUT_INVALID');
      }
    });

    it('should NOT invoke any backend API when transcript is invalid', () => {
      validateVoiceInput('', 0);
      validateVoiceInput('ab', 500);
      validateVoiceInput('   ', 1000);

      expect(mockFetch).not.toHaveBeenCalled();
    });
  });
});
