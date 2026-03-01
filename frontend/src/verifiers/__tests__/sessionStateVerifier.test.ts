/**
 * sessionStateVerifier.test.ts - Step 1 (partial): Frontend state verification
 *
 * TLA+ Properties:
 * - Reachability: Session in DRAFT → assertDraft passes (no throw)
 * - TypeInvariant: Validates session object structure
 * - ErrorConsistency: Session in FINALIZE → throws InvalidStateTransitionError
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

import { describe, it, expect } from 'vitest';
import { assertDraft } from '../sessionStateVerifier';
import { StateTransitionError } from '@/server/error_definitions/StateTransitionErrors';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const draftSession = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  state: 'DRAFT' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const finalizeSession = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  state: 'FINALIZE' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('sessionStateVerifier.assertDraft — Step 1: Validate client-side precondition', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should not throw for a session in DRAFT state', () => {
      expect(() => assertDraft(draftSession)).not.toThrow();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should accept a valid session object with DRAFT state', () => {
      const result = assertDraft(draftSession);
      // assertDraft returns void on success
      expect(result).toBeUndefined();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw InvalidStateTransitionError for FINALIZE session', () => {
      try {
        assertDraft(finalizeSession);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(StateTransitionError);
        expect((e as StateTransitionError).code).toBe('INVALID_STATE_TRANSITION');
      }
    });

    it('should include current and target state in error message', () => {
      try {
        assertDraft(finalizeSession);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as StateTransitionError).message).toContain('FINALIZE');
        expect((e as StateTransitionError).message).toContain('DRAFT');
      }
    });
  });
});
