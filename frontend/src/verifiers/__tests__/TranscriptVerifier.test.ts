/**
 * TranscriptVerifier.test.ts - Validates transcript data before rendering in UI
 *
 * TLA+ Properties:
 * - Reachability: valid transcript event → { valid: true, data }
 * - TypeInvariant: data satisfies TranscriptFinalEvent schema
 * - ErrorConsistency: invalid payload → { valid: false, errors }
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { describe, it, expect } from 'vitest';
import {
  TranscriptPayloadSchema,
  validateTranscriptPayload,
} from '../TranscriptVerifier';

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const validPayload = {
  type: 'TRANSCRIPT_FINAL' as const,
  text: 'Hello world transcript',
  sessionId: validSessionId,
};

describe('TranscriptVerifier', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should accept a valid transcript payload', () => {
      const result = TranscriptPayloadSchema.safeParse(validPayload);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data.text).toBe('Hello world transcript');
        expect(result.data.type).toBe('TRANSCRIPT_FINAL');
      }
    });

    it('should return success with data from validateTranscriptPayload', () => {
      const result = validateTranscriptPayload(validPayload);

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data.text).toBe('Hello world transcript');
      }
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should enforce type as literal TRANSCRIPT_FINAL', () => {
      const wrongType = { ...validPayload, type: 'SAY' };
      const result = TranscriptPayloadSchema.safeParse(wrongType);

      expect(result.success).toBe(false);
    });

    it('should enforce text as non-empty string', () => {
      const emptyText = { ...validPayload, text: '' };
      const result = TranscriptPayloadSchema.safeParse(emptyText);

      expect(result.success).toBe(false);
    });

    it('should enforce sessionId as UUID', () => {
      const badId = { ...validPayload, sessionId: 'not-a-uuid' };
      const result = TranscriptPayloadSchema.safeParse(badId);

      expect(result.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should reject when type is missing', () => {
      const { type, ...payload } = validPayload;
      const result = TranscriptPayloadSchema.safeParse(payload);

      expect(result.success).toBe(false);
    });

    it('should reject when text is missing', () => {
      const { text, ...payload } = validPayload;
      const result = TranscriptPayloadSchema.safeParse(payload);

      expect(result.success).toBe(false);
    });

    it('should reject when sessionId is missing', () => {
      const { sessionId, ...payload } = validPayload;
      const result = TranscriptPayloadSchema.safeParse(payload);

      expect(result.success).toBe(false);
    });

    it('should reject completely empty payload', () => {
      const result = TranscriptPayloadSchema.safeParse({});

      expect(result.success).toBe(false);
    });

    it('should return error messages from validateTranscriptPayload', () => {
      const result = validateTranscriptPayload({});

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBeGreaterThan(0);
      }
    });

    it('should reject numeric text', () => {
      const numericText = { ...validPayload, text: 123 };
      const result = TranscriptPayloadSchema.safeParse(numericText);

      expect(result.success).toBe(false);
    });
  });
});
