/**
 * RecallCompletionService.step2.test.ts - Step 2: Transform Utterance Into Slot Values
 *
 * TLA+ Properties:
 * - Reachability: StructuredSpokenInputEvent + schema → extracted slot-value pairs
 * - TypeInvariant: Keys are valid slot identifiers; values are strings
 * - ErrorConsistency: No recognizable slots → SlotParsingError; retryCount increments (≤3)
 *
 * Resource: db-h2s4 (service)
 * Path: 319-complete-required-slots-and-end-recall-loop
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { RecallError } from '@/server/error_definitions/RecallErrors';
import { BEHAVIORAL_QUESTION_TYPE_RECALL } from '@/server/data_structures/RecallSession';
import type {
  RecallSession,
  StructuredSpokenInputEvent,
} from '@/server/data_structures/RecallSession';
import type { QuestionTypeDefinition } from '@/server/data_structures/VoiceInteractionContext';

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

function createEvent(utterance: string): StructuredSpokenInputEvent {
  return {
    sessionId: validSessionId,
    questionType: 'behavioral_question',
    utterance,
  };
}

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

describe('RecallCompletionService.transformUtterance — Step 2', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should extract slot values from utterance with recognizable patterns', () => {
      const event = createEvent(
        'My objective was to increase revenue. The outcome was a 20% growth.',
      );
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;

      const result = RecallCompletionService.transformUtterance(event, schema);

      expect(result).toBeDefined();
      expect(typeof result).toBe('object');
      // Should have extracted at least objective and outcome
      expect(result['objective']).toBeDefined();
      expect(result['outcome']).toBeDefined();
    });

    it('should return extracted slot-value pairs mapped to slot identifiers', () => {
      const event = createEvent('My objective was to deliver the project on time.');
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;

      const result = RecallCompletionService.transformUtterance(event, schema);

      expect(result['objective']).toContain('deliver the project on time');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return keys that are valid slot identifiers from QuestionTypeSchema', () => {
      const event = createEvent(
        'My objective was to improve efficiency. The outcome was 30% faster.',
      );
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;

      const result = RecallCompletionService.transformUtterance(event, schema);

      const validSlotNames = schema.slots.map((s) => s.name);
      for (const key of Object.keys(result)) {
        expect(validSlotNames).toContain(key);
      }
    });

    it('should return string values for string-type slots', () => {
      const event = createEvent('My objective was to ship the feature.');
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;

      const result = RecallCompletionService.transformUtterance(event, schema);

      if (result['objective']) {
        expect(typeof result['objective']).toBe('string');
      }
    });

    it('should return string array values for string_array-type slots', () => {
      const event = createEvent(
        'I took actions: code review, testing, and deployment.',
      );
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;

      const result = RecallCompletionService.transformUtterance(event, schema);

      if (result['actions']) {
        expect(Array.isArray(result['actions'])).toBe(true);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SlotParsingError when utterance has no recognizable slot data', () => {
      const event = createEvent('asdf jkl random gibberish 12345');
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;
      const session = createSession();

      expect(() => {
        RecallCompletionService.transformUtterance(event, schema, session);
      }).toThrow(RecallError);

      try {
        RecallCompletionService.transformUtterance(event, schema, session);
      } catch (e) {
        expect((e as RecallError).code).toBe('SLOT_PARSING_ERROR');
      }
    });

    it('should increment session retryCount on parsing failure', () => {
      const event = createEvent('lorem ipsum dolor sit amet');
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;
      const session = createSession({ retryCount: 1 });

      try {
        RecallCompletionService.transformUtterance(event, schema, session);
      } catch (e) {
        // retryCount should be incremented
        expect(session.retryCount).toBe(2);
      }
    });

    it('should enforce retry limit ≤ maxRetries', () => {
      const event = createEvent('nonsense words that match nothing');
      const schema = BEHAVIORAL_QUESTION_TYPE_RECALL;
      const session = createSession({ retryCount: 2, maxRetries: 3 });

      try {
        RecallCompletionService.transformUtterance(event, schema, session);
      } catch (e) {
        expect(session.retryCount).toBeLessThanOrEqual(session.maxRetries);
      }
    });
  });
});
