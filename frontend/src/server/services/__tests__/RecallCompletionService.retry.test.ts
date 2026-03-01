/**
 * RecallCompletionService.retry.test.ts - Feedback Loop Enforcement (Retry Limit)
 *
 * Tests that the retry count is properly tracked and enforced, and that
 * IncompleteInformationError is emitted when the limit is exceeded.
 *
 * Resource: db-h2s4 (service)
 * Path: 319-complete-required-slots-and-end-recall-loop
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { RecallError } from '@/server/error_definitions/RecallErrors';
import { BEHAVIORAL_QUESTION_TYPE_RECALL } from '@/server/data_structures/RecallSession';
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

function createSession(overrides: Partial<RecallSession> = {}): RecallSession {
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallCompletionService — Feedback Loop Enforcement (Retry Limit)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should increment retryCount when parsing fails', () => {
    const session = createSession({ retryCount: 0 });
    const event = {
      sessionId: validSessionId,
      questionType: 'behavioral_question',
      utterance: 'random gibberish 12345 xyzzy',
    };

    try {
      RecallCompletionService.transformUtterance(
        event,
        BEHAVIORAL_QUESTION_TYPE_RECALL,
        session,
      );
    } catch {
      // Expected to throw
    }

    expect(session.retryCount).toBe(1);
  });

  it('should keep session active when retryCount < maxRetries', () => {
    const session = createSession({ retryCount: 1, maxRetries: 3 });
    const event = {
      sessionId: validSessionId,
      questionType: 'behavioral_question',
      utterance: 'nonsense words that match nothing',
    };

    try {
      RecallCompletionService.transformUtterance(
        event,
        BEHAVIORAL_QUESTION_TYPE_RECALL,
        session,
      );
    } catch {
      // Expected
    }

    expect(session.active).toBe(true);
    expect(session.retryCount).toBe(2);
  });

  it('should emit IncompleteInformationError when retryCount reaches maxRetries', () => {
    const session = createSession({ retryCount: 2, maxRetries: 3 });
    const event = {
      sessionId: validSessionId,
      questionType: 'behavioral_question',
      utterance: 'completely unrecognizable input zzz',
    };

    try {
      RecallCompletionService.transformUtterance(
        event,
        BEHAVIORAL_QUESTION_TYPE_RECALL,
        session,
      );
      expect.fail('Should have thrown');
    } catch (e) {
      expect(e).toBeInstanceOf(RecallError);
      expect((e as RecallError).code).toBe('INCOMPLETE_INFORMATION_ERROR');
    }
  });

  it('should set session.active to remain true until limit exceeded', () => {
    const session = createSession({ retryCount: 1, maxRetries: 3 });
    const event = {
      sessionId: validSessionId,
      questionType: 'behavioral_question',
      utterance: 'asdf jkl random',
    };

    try {
      RecallCompletionService.transformUtterance(
        event,
        BEHAVIORAL_QUESTION_TYPE_RECALL,
        session,
      );
    } catch {
      // Expected
    }

    // Session should still be active — we haven't exceeded the limit yet
    expect(session.active).toBe(true);
  });

  it('should have retryCount = 3 when max retries is 3 and limit is reached', () => {
    const session = createSession({ retryCount: 2, maxRetries: 3 });
    const event = {
      sessionId: validSessionId,
      questionType: 'behavioral_question',
      utterance: 'completely unrecognizable',
    };

    try {
      RecallCompletionService.transformUtterance(
        event,
        BEHAVIORAL_QUESTION_TYPE_RECALL,
        session,
      );
    } catch {
      // Expected
    }

    expect(session.retryCount).toBe(3);
  });
});
