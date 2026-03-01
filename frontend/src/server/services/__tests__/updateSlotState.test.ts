/**
 * updateSlotState.test.ts - Step 2: Update slot state
 *
 * TLA+ Properties:
 * - Reachability: Merge partial data into existing state
 * - TypeInvariant: Updated state matches SlotState schema; confirmed slots unchanged
 * - ErrorConsistency: Invalid slot value → SlotValidationError
 *
 * Resource: db-h2s4 (service)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import {
  SlotStateSchema,
  BEHAVIORAL_QUESTION_TYPE,
} from '@/server/data_structures/VoiceInteractionContext';
import type {
  VoiceInteractionContext,
  PartialSlotData,
  SlotState,
} from '@/server/data_structures/VoiceInteractionContext';

// Mock the recall voice logger
vi.mock('@/server/logging/recallVoiceLogger', () => ({
  recallVoiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { VoiceRecallService } from '../VoiceRecallService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createContext(overrides: Partial<VoiceInteractionContext> = {}): VoiceInteractionContext {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE,
    slotState: { slots: [] },
    retryCount: 0,
    maxRetries: 2,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VoiceRecallService.updateSlotState — Step 2: Update slot state', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should merge partial data with actions into empty state', () => {
      const context = createContext({
        slotState: {
          slots: [
            { name: 'objective', value: 'Increase sales', confirmed: true },
          ],
        },
      });

      const partialData: PartialSlotData = {
        slots: [
          { name: 'actions', value: ['cold calling', 'email campaigns', 'social outreach'] },
        ],
      };

      const result = VoiceRecallService.updateSlotState(context, partialData);

      expect(result.slots).toHaveLength(2);
      expect(result.slots.find((s) => s.name === 'objective')).toBeDefined();
      expect(result.slots.find((s) => s.name === 'actions')).toBeDefined();
    });

    it('should contain both confirmed objective and new actions', () => {
      const context = createContext({
        slotState: {
          slots: [
            { name: 'objective', value: 'Increase sales', confirmed: true },
          ],
        },
      });

      const partialData: PartialSlotData = {
        slots: [
          { name: 'actions', value: ['cold calling', 'email campaigns', 'networking'] },
        ],
      };

      const result = VoiceRecallService.updateSlotState(context, partialData);

      const objectiveSlot = result.slots.find((s) => s.name === 'objective');
      const actionsSlot = result.slots.find((s) => s.name === 'actions');

      expect(objectiveSlot?.value).toBe('Increase sales');
      expect(actionsSlot?.value).toEqual(['cold calling', 'email campaigns', 'networking']);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result conforming to SlotState schema', () => {
      const context = createContext();
      const partialData: PartialSlotData = {
        slots: [{ name: 'objective', value: 'Deliver project on time' }],
      };

      const result = VoiceRecallService.updateSlotState(context, partialData);

      const parsed = SlotStateSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should not overwrite confirmed slots', () => {
      const context = createContext({
        slotState: {
          slots: [
            { name: 'objective', value: 'Original objective', confirmed: true },
          ],
        },
      });

      const partialData: PartialSlotData = {
        slots: [{ name: 'objective', value: 'New objective' }],
      };

      const result = VoiceRecallService.updateSlotState(context, partialData);

      const objectiveSlot = result.slots.find((s) => s.name === 'objective');
      expect(objectiveSlot?.value).toBe('Original objective');
      expect(objectiveSlot?.confirmed).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SlotValidationError for empty string slot value', () => {
      const context = createContext();
      const partialData: PartialSlotData = {
        slots: [{ name: 'objective', value: '   ' }],
      };

      try {
        VoiceRecallService.updateSlotState(context, partialData);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('SLOT_VALIDATION_FAILED');
      }
    });

    it('should throw SlotValidationError for actions array below minimum', () => {
      const context = createContext();
      const partialData: PartialSlotData = {
        slots: [{ name: 'actions', value: ['only one action'] }],
      };

      try {
        VoiceRecallService.updateSlotState(context, partialData);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('SLOT_VALIDATION_FAILED');
      }
    });
  });
});
