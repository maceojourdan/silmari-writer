/**
 * FinalizeEligibilityVerifier.test.ts - Verifies finalized status and evaluates SMS opt-in eligibility.
 *
 * TLA+ Properties:
 * - Reachability: Given status="FINALIZED", smsOptIn=false -> { eligible: false }
 *                 Given status="FINALIZED", smsOptIn=true  -> { eligible: true }
 * - TypeInvariant: Decision matches EligibilityDecisionSchema (safeParse succeeds)
 * - ErrorConsistency:
 *     - status="DRAFT"     -> FinalizeWithoutSmsError with code INVALID_FINALIZE_STATE
 *     - status="COMPLETED" -> FinalizeWithoutSmsError with code INVALID_FINALIZE_STATE
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { describe, it, expect } from 'vitest';
import { FinalizeEligibilityVerifier } from '../FinalizeEligibilityVerifier';
import { FinalizeWithoutSmsError } from '@/server/error_definitions/FinalizeWithoutSmsErrors';
import {
  EligibilityDecisionSchema,
  type AnswerWithUserPreference,
} from '@/server/data_structures/FinalizeCompletion';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = 'a1a1a1a1-a1a1-a1a1-a1a1-a1a1a1a1a1a1';

const finalizedSmsOptOut: AnswerWithUserPreference = {
  id: answerId,
  status: 'FINALIZED',
  user: { smsOptIn: false },
};

const finalizedSmsOptIn: AnswerWithUserPreference = {
  id: answerId,
  status: 'FINALIZED',
  user: { smsOptIn: true },
};

const draftAnswer: AnswerWithUserPreference = {
  id: answerId,
  status: 'DRAFT',
  user: { smsOptIn: false },
};

const completedAnswer: AnswerWithUserPreference = {
  id: answerId,
  status: 'COMPLETED',
  user: { smsOptIn: false },
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeEligibilityVerifier — Verify finalized status and SMS eligibility', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return { eligible: false } when status is FINALIZED and smsOptIn is false', () => {
      const decision = FinalizeEligibilityVerifier.verify(finalizedSmsOptOut);
      expect(decision).toEqual({ eligible: false });
    });

    it('should return { eligible: true } when status is FINALIZED and smsOptIn is true', () => {
      const decision = FinalizeEligibilityVerifier.verify(finalizedSmsOptIn);
      expect(decision).toEqual({ eligible: true });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a decision that matches EligibilityDecisionSchema', () => {
      const decision = FinalizeEligibilityVerifier.verify(finalizedSmsOptOut);
      const result = EligibilityDecisionSchema.safeParse(decision);
      expect(result.success).toBe(true);
    });

    it('should return a decision matching EligibilityDecisionSchema when eligible is true', () => {
      const decision = FinalizeEligibilityVerifier.verify(finalizedSmsOptIn);
      const result = EligibilityDecisionSchema.safeParse(decision);
      expect(result.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw FinalizeWithoutSmsError with INVALID_FINALIZE_STATE when status is DRAFT', () => {
      try {
        FinalizeEligibilityVerifier.verify(draftAnswer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('INVALID_FINALIZE_STATE');
        expect((e as FinalizeWithoutSmsError).statusCode).toBe(422);
      }
    });

    it('should throw FinalizeWithoutSmsError with INVALID_FINALIZE_STATE when status is COMPLETED', () => {
      try {
        FinalizeEligibilityVerifier.verify(completedAnswer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeWithoutSmsError);
        expect((e as FinalizeWithoutSmsError).code).toBe('INVALID_FINALIZE_STATE');
        expect((e as FinalizeWithoutSmsError).statusCode).toBe(422);
      }
    });
  });
});
