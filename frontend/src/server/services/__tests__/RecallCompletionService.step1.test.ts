/**
 * RecallCompletionService.step1.test.ts - Step 1: Capture Additional Spoken Input
 *
 * TLA+ Properties:
 * - Reachability: Active session + utterance → StructuredSpokenInputEvent returned
 * - TypeInvariant: Return type is StructuredSpokenInputEvent with correct field types
 * - ErrorConsistency: Inactive session → InvalidRecallStateError thrown
 *
 * Resource: db-h2s4 (service)
 * Path: 319-complete-required-slots-and-end-recall-loop
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { RecallError } from '@/server/error_definitions/RecallErrors';
import {
  StructuredSpokenInputEventSchema,
  BEHAVIORAL_QUESTION_TYPE_RECALL,
} from '@/server/data_structures/RecallSession';
import type { RecallSession } from '@/server/data_structures/RecallSession';

// Mock the recall completion logger
vi.mock('@/server/logging/recallCompletionLogger', () => ({
  recallCompletionLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { RecallCompletionService } from '../RecallCompletionService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createActiveSession(overrides: Partial<RecallSession> = {}): RecallSession {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE_RECALL,
    slotState: { slots: [] },
    active: true,
    retryCount: 0,
    maxRetries: 3,
    ...overrides,
  };
}

function createInactiveSession(overrides: Partial<RecallSession> = {}): RecallSession {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE_RECALL,
    slotState: { slots: [] },
    active: false,
    retryCount: 0,
    maxRetries: 3,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallCompletionService.captureAdditionalInput — Step 1', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return StructuredSpokenInputEvent when session is active', () => {
      const session = createActiveSession();
      const utterance = 'I increased revenue by 20%';

      const result = RecallCompletionService.captureAdditionalInput(session, utterance);

      expect(result).toBeDefined();
      expect(result.sessionId).toBe(validSessionId);
      expect(result.questionType).toBe('behavioral_question');
      expect(result.utterance).toBe(utterance);
    });

    it('should associate utterance with the active question_type session', () => {
      const session = createActiveSession();
      const utterance = 'My objective was to improve team efficiency';

      const result = RecallCompletionService.captureAdditionalInput(session, utterance);

      expect(result.sessionId).toBe(session.sessionId);
      expect(result.questionType).toBe(session.questionType.name);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result conforming to StructuredSpokenInputEvent schema', () => {
      const session = createActiveSession();
      const utterance = 'I increased revenue by 20%';

      const result = RecallCompletionService.captureAdditionalInput(session, utterance);

      const parsed = StructuredSpokenInputEventSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have utterance as string', () => {
      const session = createActiveSession();
      const utterance = 'The outcome was a 30% improvement';

      const result = RecallCompletionService.captureAdditionalInput(session, utterance);

      expect(typeof result.utterance).toBe('string');
    });

    it('should have sessionId as string', () => {
      const session = createActiveSession();
      const utterance = 'I led the project';

      const result = RecallCompletionService.captureAdditionalInput(session, utterance);

      expect(typeof result.sessionId).toBe('string');
    });

    it('should have questionType as string', () => {
      const session = createActiveSession();
      const utterance = 'I faced budget constraints';

      const result = RecallCompletionService.captureAdditionalInput(session, utterance);

      expect(typeof result.questionType).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw InvalidRecallStateError when session is inactive', () => {
      const session = createInactiveSession();
      const utterance = 'I increased revenue by 20%';

      expect(() => {
        RecallCompletionService.captureAdditionalInput(session, utterance);
      }).toThrow(RecallError);

      try {
        RecallCompletionService.captureAdditionalInput(session, utterance);
      } catch (e) {
        expect((e as RecallError).code).toBe('INVALID_RECALL_STATE');
      }
    });

    it('should throw InvalidRecallStateError with descriptive message', () => {
      const session = createInactiveSession();
      const utterance = 'Some input';

      try {
        RecallCompletionService.captureAdditionalInput(session, utterance);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(RecallError);
        expect((e as RecallError).message).toContain('active');
      }
    });
  });
});
