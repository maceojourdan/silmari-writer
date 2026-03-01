/**
 * SessionModificationVerifier.test.ts - Frontend verification for session modification
 *
 * TLA+ Properties:
 * - Reachability: valid payload passes verification.
 * - TypeInvariant: payload matches { sessionId: string; action: 'ADD_VOICE' | 'FINALIZE' }
 * - ErrorConsistency: invalid payload (missing sessionId) returns validation errors.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 309-reject-modifications-to-finalized-session
 */

import { describe, it, expect } from 'vitest';
import {
  validateModifySessionPayload,
  ModifySessionPayloadSchema,
} from '../SessionModificationVerifier';

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SessionModificationVerifier — Frontend verification', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return success for valid payload with ADD_VOICE', () => {
      const result = validateModifySessionPayload({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        action: 'ADD_VOICE',
      });

      expect(result.success).toBe(true);
    });

    it('should return success for valid payload with FINALIZE', () => {
      const result = validateModifySessionPayload({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        action: 'FINALIZE',
      });

      expect(result.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate payload matches schema { sessionId: string; action: ADD_VOICE | FINALIZE }', () => {
      const valid = ModifySessionPayloadSchema.safeParse({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        action: 'ADD_VOICE',
      });
      expect(valid.success).toBe(true);

      const invalid = ModifySessionPayloadSchema.safeParse({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        action: 'INVALID',
      });
      expect(invalid.success).toBe(false);
    });

    it('should return typed data on success', () => {
      const result = validateModifySessionPayload({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        action: 'ADD_VOICE',
      });

      if (result.success) {
        expect(result.data.sessionId).toBe('550e8400-e29b-41d4-a716-446655440000');
        expect(result.data.action).toBe('ADD_VOICE');
      } else {
        expect.fail('Expected success');
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return errors when sessionId is missing', () => {
      const result = validateModifySessionPayload({
        action: 'ADD_VOICE',
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBeGreaterThan(0);
        expect(result.errors.some((e) => e.includes('sessionId'))).toBe(true);
      }
    });

    it('should return errors when action is missing', () => {
      const result = validateModifySessionPayload({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBeGreaterThan(0);
      }
    });

    it('should return errors for empty sessionId', () => {
      const result = validateModifySessionPayload({
        sessionId: '',
        action: 'ADD_VOICE',
      });

      expect(result.success).toBe(false);
    });

    it('should return errors for completely empty payload', () => {
      const result = validateModifySessionPayload({});

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBeGreaterThan(0);
      }
    });
  });
});
