/**
 * Tests for draftPreconditionsVerifier
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Valid payload → success
 * - TypeInvariant: Payload matches Zod schema
 * - ErrorConsistency: Missing/empty storyRecordId → validation failure with message
 */

import { describe, it, expect } from 'vitest';
import {
  DraftPreconditionsPayloadSchema,
  validateDraftPreconditions,
  type DraftPreconditionsPayload,
} from '../draftPreconditionsVerifier';

describe('draftPreconditionsVerifier — Path 327', () => {
  const validPayload: DraftPreconditionsPayload = {
    storyRecordId: 'story-record-abc-123',
  };

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should accept a valid payload with storyRecordId', () => {
      const result = DraftPreconditionsPayloadSchema.safeParse(validPayload);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data).toEqual(validPayload);
      }
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should enforce string type on storyRecordId', () => {
      const result = DraftPreconditionsPayloadSchema.safeParse({
        storyRecordId: 123,
      });
      expect(result.success).toBe(false);
    });

    it('should reject null storyRecordId', () => {
      const result = DraftPreconditionsPayloadSchema.safeParse({
        storyRecordId: null,
      });
      expect(result.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should reject when storyRecordId is missing', () => {
      const result = DraftPreconditionsPayloadSchema.safeParse({});
      expect(result.success).toBe(false);
    });

    it('should reject empty string storyRecordId', () => {
      const result = DraftPreconditionsPayloadSchema.safeParse({
        storyRecordId: '',
      });
      expect(result.success).toBe(false);
    });

    it('should reject completely empty payload', () => {
      const result = DraftPreconditionsPayloadSchema.safeParse({});
      expect(result.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // validateDraftPreconditions helper
  // -------------------------------------------------------------------------

  describe('validateDraftPreconditions helper', () => {
    it('should return { valid: true } on valid payload', () => {
      const result = validateDraftPreconditions(validPayload);
      expect(result.valid).toBe(true);
    });

    it('should return { valid: false, message } on invalid payload', () => {
      const result = validateDraftPreconditions({});
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.message).toBeDefined();
        expect(result.message!.length).toBeGreaterThan(0);
      }
    });

    it('should include field name in validation message on error', () => {
      const result = validateDraftPreconditions({ storyRecordId: '' });
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.message).toContain('storyRecordId');
      }
    });
  });
});
