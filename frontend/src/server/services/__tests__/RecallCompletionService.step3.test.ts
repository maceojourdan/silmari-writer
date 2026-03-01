/**
 * RecallCompletionService.step3.test.ts - Step 3: Merge With Existing Recall State
 *
 * TLA+ Properties:
 * - Reachability: session.slots partially filled + extracted values → merged slot state
 * - TypeInvariant: session.slots matches QuestionTypeSchema shape; no unknown keys
 * - ErrorConsistency: extracted contains invalid slot key → SlotValidationError
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

function createSessionWithSlots(
  filledSlots: Record<string, string | string[] | null>,
  overrides: Partial<RecallSession> = {},
): RecallSession {
  const slots = Object.entries(filledSlots)
    .filter(([, v]) => v !== null)
    .map(([name, value]) => ({
      name,
      value: value as string | string[],
      confirmed: false,
    }));

  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE_RECALL,
    slotState: { slots },
    active: true,
    retryCount: 0,
    maxRetries: 3,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallCompletionService.mergeSlots — Step 3', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should fill a previously null slot with extracted value', () => {
      const session = createSessionWithSlots({
        objective: null,
        outcome: null,
      });
      const extracted: Record<string, string | string[]> = {
        objective: 'Increase revenue',
      };

      RecallCompletionService.mergeSlots(session, extracted);

      const objectiveSlot = session.slotState.slots.find((s) => s.name === 'objective');
      expect(objectiveSlot).toBeDefined();
      expect(objectiveSlot!.value).toBe('Increase revenue');
    });

    it('should preserve already-filled slots when merging new values', () => {
      const session = createSessionWithSlots({
        objective: 'Existing objective',
      });
      const extracted: Record<string, string | string[]> = {
        outcome: 'Revenue grew 20%',
      };

      RecallCompletionService.mergeSlots(session, extracted);

      const objectiveSlot = session.slotState.slots.find((s) => s.name === 'objective');
      const outcomeSlot = session.slotState.slots.find((s) => s.name === 'outcome');
      expect(objectiveSlot!.value).toBe('Existing objective');
      expect(outcomeSlot!.value).toBe('Revenue grew 20%');
    });

    it('should overwrite unfilled slots with new extracted values', () => {
      const session = createSessionWithSlots({});
      const extracted: Record<string, string | string[]> = {
        objective: 'New objective value',
        actions: ['action1', 'action2', 'action3'],
      };

      RecallCompletionService.mergeSlots(session, extracted);

      const objectiveSlot = session.slotState.slots.find((s) => s.name === 'objective');
      const actionsSlot = session.slotState.slots.find((s) => s.name === 'actions');
      expect(objectiveSlot!.value).toBe('New objective value');
      expect(actionsSlot!.value).toEqual(['action1', 'action2', 'action3']);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should produce slot state matching QuestionTypeSchema shape', () => {
      const session = createSessionWithSlots({});
      const extracted: Record<string, string | string[]> = {
        objective: 'Test objective',
      };

      RecallCompletionService.mergeSlots(session, extracted);

      const validSlotNames = session.questionType.slots.map((s) => s.name);
      for (const slot of session.slotState.slots) {
        expect(validSlotNames).toContain(slot.name);
      }
    });

    it('should not introduce unknown keys into slot state', () => {
      const session = createSessionWithSlots({
        objective: 'Test',
      });
      const extracted: Record<string, string | string[]> = {
        outcome: 'Good result',
      };

      RecallCompletionService.mergeSlots(session, extracted);

      const validSlotNames = session.questionType.slots.map((s) => s.name);
      for (const slot of session.slotState.slots) {
        expect(validSlotNames).toContain(slot.name);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SlotValidationError when extracted contains invalid slot key', () => {
      const session = createSessionWithSlots({});
      const extracted: Record<string, string | string[]> = {
        invalidSlot: 'value',
      };

      expect(() => {
        RecallCompletionService.mergeSlots(session, extracted);
      }).toThrow(RecallError);

      try {
        RecallCompletionService.mergeSlots(session, extracted);
      } catch (e) {
        expect((e as RecallError).code).toBe('SLOT_VALIDATION_ERROR');
      }
    });

    it('should throw SlotValidationError with descriptive message for unknown keys', () => {
      const session = createSessionWithSlots({});
      const extracted: Record<string, string | string[]> = {
        totallyBogus: 'nonsense',
      };

      try {
        RecallCompletionService.mergeSlots(session, extracted);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(RecallError);
        expect((e as RecallError).message).toContain('totallyBogus');
      }
    });
  });
});
