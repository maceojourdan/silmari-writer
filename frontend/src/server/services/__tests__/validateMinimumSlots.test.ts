/**
 * validateMinimumSlots.test.ts - Step 3: Validate minimum required slots
 *
 * TLA+ Properties:
 * - Reachability: Slot state missing 'outcome' → missingSlots includes 'outcome'
 * - TypeInvariant: Output conforms to MinimumSlotValidationResult schema
 * - ErrorConsistency: Missing minimumRequiredSlots → ConfigurationError
 *
 * Resource: db-h2s4 (service)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import {
  MinimumSlotValidationResultSchema,
  BEHAVIORAL_QUESTION_TYPE,
} from '@/server/data_structures/VoiceInteractionContext';
import type {
  VoiceInteractionContext,
  QuestionTypeDefinition,
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

describe('VoiceRecallService.validateMinimumRequiredSlots — Step 3: Validate minimum required slots', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return missingSlots including "outcome" when outcome is not filled', () => {
      const context = createContext({
        slotState: {
          slots: [
            { name: 'objective', value: 'Increase sales', confirmed: true },
            { name: 'actions', value: ['call', 'email', 'present'], confirmed: false },
            { name: 'obstacles', value: ['budget constraints'], confirmed: false },
            { name: 'roleClarity', value: 'Sales lead', confirmed: false },
            // outcome is missing!
          ],
        },
      });

      const result = VoiceRecallService.validateMinimumRequiredSlots(context);

      expect(result.missingSlots).toContain('outcome');
      expect(result.valid).toBe(false);
    });

    it('should return valid=true when all minimum slots are filled', () => {
      const context = createContext({
        slotState: {
          slots: [
            { name: 'objective', value: 'Increase sales', confirmed: true },
            { name: 'actions', value: ['call', 'email', 'present'], confirmed: false },
            { name: 'obstacles', value: ['budget constraints'], confirmed: false },
            { name: 'outcome', value: '20% increase in revenue', confirmed: false },
            { name: 'roleClarity', value: 'Sales lead', confirmed: false },
          ],
        },
      });

      const result = VoiceRecallService.validateMinimumRequiredSlots(context);

      expect(result.valid).toBe(true);
      expect(result.missingSlots).toHaveLength(0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result conforming to MinimumSlotValidationResult schema', () => {
      const context = createContext({
        slotState: {
          slots: [
            { name: 'objective', value: 'Increase sales', confirmed: true },
          ],
        },
      });

      const result = VoiceRecallService.validateMinimumRequiredSlots(context);

      const parsed = MinimumSlotValidationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw ConfigurationError when question_type has no minimumRequiredSlots', () => {
      const badQuestionType: QuestionTypeDefinition = {
        name: 'broken_type',
        slots: [{ name: 'objective', required: true, type: 'string' }],
        minimumRequiredSlots: [], // empty!
      };

      const context = createContext({
        questionType: badQuestionType,
      });

      try {
        VoiceRecallService.validateMinimumRequiredSlots(context);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('CONFIGURATION_ERROR');
      }
    });
  });
});
