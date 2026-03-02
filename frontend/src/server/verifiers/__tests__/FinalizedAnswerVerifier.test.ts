/**
 * FinalizedAnswerVerifier.test.ts - Verifies answer is finalized and locked for export.
 *
 * TLA+ Properties:
 * - Reachability: Given finalized=true, locked=true → no error thrown
 * - TypeInvariant: Verifier operates on Answer type from db-f8n5
 * - ErrorConsistency:
 *     - Not finalized → AnswerErrors.ANSWER_NOT_LOCKED
 *     - Not locked → AnswerErrors.ANSWER_NOT_LOCKED
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 334-export-or-copy-finalized-answer
 */

import { describe, it, expect } from 'vitest';
import { FinalizedAnswerVerifier } from '../FinalizedAnswerVerifier';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';
import type { Answer } from '@/server/data_structures/Answer';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const finalizedLockedAnswer: Answer = {
  id: answerId,
  status: 'FINALIZED',
  finalized: true,
  editable: false,
  locked: true,
  content: 'My finalized answer content.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const notFinalizedAnswer: Answer = {
  id: answerId,
  status: 'COMPLETED',
  finalized: false,
  editable: true,
  locked: false,
  content: 'My completed answer content.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const finalizedButNotLockedAnswer: Answer = {
  id: answerId,
  status: 'FINALIZED',
  finalized: true,
  editable: false,
  locked: false,
  content: 'My finalized but not locked answer content.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizedAnswerVerifier — Verify finalized and locked state', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should not throw when answer is finalized and locked', () => {
      expect(() => {
        FinalizedAnswerVerifier.ensureFinalizedLocked(finalizedLockedAnswer);
      }).not.toThrow();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should accept Answer type from db-f8n5 data structure', () => {
      // The fact that TypeScript compiles this test proves the type invariant
      const answer: Answer = finalizedLockedAnswer;
      expect(() => {
        FinalizedAnswerVerifier.ensureFinalizedLocked(answer);
      }).not.toThrow();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw ANSWER_NOT_LOCKED when not finalized', () => {
      try {
        FinalizedAnswerVerifier.ensureFinalizedLocked(notFinalizedAnswer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_LOCKED');
        expect((e as AnswerError).statusCode).toBe(422);
      }
    });

    it('should throw ANSWER_NOT_LOCKED when finalized but not locked', () => {
      try {
        FinalizedAnswerVerifier.ensureFinalizedLocked(finalizedButNotLockedAnswer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(AnswerError);
        expect((e as AnswerError).code).toBe('ANSWER_NOT_LOCKED');
        expect((e as AnswerError).statusCode).toBe(422);
      }
    });
  });
});
