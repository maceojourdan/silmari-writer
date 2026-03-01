/**
 * Tests for AlignmentVerifier - Step 2: Perform client-side alignment validation
 *
 * Path: 314-prevent-confirmation-of-misaligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Valid payload + matching rules → status "aligned"
 * - TypeInvariant: Return type is AlignmentResult { status, messageKey? }
 * - ErrorConsistency (misaligned): Payload violates rule → status "misaligned", messageKey "STORY_MISALIGNED"
 * - ErrorConsistency (rules unavailable): rules = null → status "misaligned", messageKey "ALIGNMENT_RULES_UNAVAILABLE"
 */

import { describe, it, expect } from 'vitest';
import { AlignmentVerifier } from '../AlignmentVerifier';
import type { ConfirmationPayload, AlignmentRules, AlignmentResult } from '../AlignmentVerifier';

// ---------------------------------------------------------------------------
// Test data
// ---------------------------------------------------------------------------

const alignedPayload: ConfirmationPayload = {
  storyId: 'story-001',
  questionId: 'q-001',
  jobId: 'job-001',
};

const matchingRules: AlignmentRules = {
  activeQuestionId: 'q-001',
  stories: [
    { id: 'story-001', questionId: 'q-001', status: 'AVAILABLE' },
    { id: 'story-002', questionId: 'q-001', status: 'AVAILABLE' },
  ],
};

describe('AlignmentVerifier - Step 2: Client-side alignment validation', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return status "aligned" for a valid payload with matching rules', () => {
      const result = AlignmentVerifier.validate(alignedPayload, matchingRules);
      expect(result.status).toBe('aligned');
    });

    it('should not set messageKey when aligned', () => {
      const result = AlignmentVerifier.validate(alignedPayload, matchingRules);
      expect(result.messageKey).toBeUndefined();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object with status property of type "aligned" | "misaligned"', () => {
      const alignedResult = AlignmentVerifier.validate(alignedPayload, matchingRules);
      expect(['aligned', 'misaligned']).toContain(alignedResult.status);
      expect(typeof alignedResult.status).toBe('string');

      const misalignedResult = AlignmentVerifier.validate(alignedPayload, null);
      expect(['aligned', 'misaligned']).toContain(misalignedResult.status);
    });

    it('should have optional messageKey property of type string', () => {
      const aligned = AlignmentVerifier.validate(alignedPayload, matchingRules);
      expect(aligned.messageKey === undefined || typeof aligned.messageKey === 'string').toBe(true);

      const misaligned = AlignmentVerifier.validate(alignedPayload, null);
      expect(typeof misaligned.messageKey).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency (misaligned)
  // -------------------------------------------------------------------------

  describe('ErrorConsistency (misaligned)', () => {
    it('should return "misaligned" when story questionId does not match active question', () => {
      const mismatchedPayload: ConfirmationPayload = {
        storyId: 'story-003',
        questionId: 'q-001',
        jobId: 'job-001',
      };

      const rulesWithMismatch: AlignmentRules = {
        activeQuestionId: 'q-001',
        stories: [
          { id: 'story-003', questionId: 'q-999', status: 'AVAILABLE' }, // wrong questionId
        ],
      };

      const result = AlignmentVerifier.validate(mismatchedPayload, rulesWithMismatch);
      expect(result.status).toBe('misaligned');
      expect(result.messageKey).toBe('STORY_MISALIGNED');
    });

    it('should return "misaligned" when story status is not AVAILABLE', () => {
      const payload: ConfirmationPayload = {
        storyId: 'story-001',
        questionId: 'q-001',
        jobId: 'job-001',
      };

      const rulesExcluded: AlignmentRules = {
        activeQuestionId: 'q-001',
        stories: [
          { id: 'story-001', questionId: 'q-001', status: 'EXCLUDED' },
        ],
      };

      const result = AlignmentVerifier.validate(payload, rulesExcluded);
      expect(result.status).toBe('misaligned');
      expect(result.messageKey).toBe('STORY_MISALIGNED');
    });

    it('should return "misaligned" when story is not found in rules', () => {
      const unknownStoryPayload: ConfirmationPayload = {
        storyId: 'story-unknown',
        questionId: 'q-001',
        jobId: 'job-001',
      };

      const result = AlignmentVerifier.validate(unknownStoryPayload, matchingRules);
      expect(result.status).toBe('misaligned');
      expect(result.messageKey).toBe('STORY_MISALIGNED');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency (rules unavailable)
  // -------------------------------------------------------------------------

  describe('ErrorConsistency (rules unavailable)', () => {
    it('should return "misaligned" when rules are null', () => {
      const result = AlignmentVerifier.validate(alignedPayload, null);
      expect(result.status).toBe('misaligned');
    });

    it('should set messageKey to ALIGNMENT_RULES_UNAVAILABLE when rules are null', () => {
      const result = AlignmentVerifier.validate(alignedPayload, null);
      expect(result.messageKey).toBe('ALIGNMENT_RULES_UNAVAILABLE');
    });
  });
});
