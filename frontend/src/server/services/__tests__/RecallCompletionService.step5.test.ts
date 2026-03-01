/**
 * RecallCompletionService.step5.test.ts - Step 5: Confirm Completion And Terminate Recall Loop
 *
 * TLA+ Properties:
 * - Reachability: validation.complete = true → session.active = false + confirmation message
 * - TypeInvariant: session.active is boolean; confirmation is string
 * - ErrorConsistency: State persistence throws → RecallStateTransitionError + logger.error called
 *
 * Resource: db-h2s4 (service)
 * Path: 319-complete-required-slots-and-end-recall-loop
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { RecallError } from '@/server/error_definitions/RecallErrors';
import { BEHAVIORAL_QUESTION_TYPE_RECALL } from '@/server/data_structures/RecallSession';
import type { RecallSession } from '@/server/data_structures/RecallSession';

// Mock the recall completion logger (vi.hoisted avoids the TDZ issue with vi.mock)
const mockLogger = vi.hoisted(() => ({
  info: vi.fn(),
  warn: vi.fn(),
  error: vi.fn(),
}));

vi.mock('@/server/logging/recallCompletionLogger', () => ({
  recallCompletionLogger: mockLogger,
}));

import { RecallCompletionService } from '../RecallCompletionService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createCompletedSession(): RecallSession {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE_RECALL,
    slotState: {
      slots: [
        { name: 'objective', value: 'Increase revenue by 20%', confirmed: false },
        { name: 'actions', value: ['cold calling', 'email campaigns', 'social media outreach'], confirmed: false },
        { name: 'obstacles', value: ['budget constraints'], confirmed: false },
        { name: 'outcome', value: 'Revenue grew by 25%', confirmed: false },
        { name: 'roleClarity', value: 'I was the sales team lead', confirmed: false },
      ],
    },
    active: true,
    retryCount: 0,
    maxRetries: 3,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallCompletionService.confirmCompletion — Step 5', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should set session.active to false when called', () => {
      const session = createCompletedSession();
      expect(session.active).toBe(true);

      RecallCompletionService.confirmCompletion(session);

      expect(session.active).toBe(false);
    });

    it('should return a confirmation message string', () => {
      const session = createCompletedSession();

      const result = RecallCompletionService.confirmCompletion(session);

      expect(result).toBeDefined();
      expect(typeof result).toBe('string');
      expect(result.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should ensure session.active is boolean after completion', () => {
      const session = createCompletedSession();

      RecallCompletionService.confirmCompletion(session);

      expect(typeof session.active).toBe('boolean');
      expect(session.active).toBe(false);
    });

    it('should return confirmation as a string', () => {
      const session = createCompletedSession();

      const result = RecallCompletionService.confirmCompletion(session);

      expect(typeof result).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw RecallStateTransitionError when state persistence fails', () => {
      const session = createCompletedSession();

      // Make session state update fail by using a frozen object with a
      // custom persist callback that throws
      const persistFn = vi.fn().mockImplementation(() => {
        throw new Error('Database connection lost');
      });

      expect(() => {
        RecallCompletionService.confirmCompletion(session, persistFn);
      }).toThrow(RecallError);

      try {
        RecallCompletionService.confirmCompletion(session, persistFn);
      } catch (e) {
        expect((e as RecallError).code).toBe('RECALL_STATE_TRANSITION_ERROR');
      }
    });

    it('should call logger.error when state persistence fails', () => {
      const session = createCompletedSession();
      const persistFn = vi.fn().mockImplementation(() => {
        throw new Error('Database timeout');
      });

      try {
        RecallCompletionService.confirmCompletion(session, persistFn);
      } catch {
        // Expected
      }

      expect(mockLogger.error).toHaveBeenCalled();
    });
  });
});
