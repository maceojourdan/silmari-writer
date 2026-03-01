/**
 * MinimumSlotValidator.test.ts - Step 3: Validate minimum required slots
 *
 * TLA+ Properties:
 * - Reachability: Pass complete slot object → expect { valid: true }
 * - TypeInvariant: Return type is { valid: boolean; missing?: string[] }
 * - ErrorConsistency: Pass object missing 'outcome' → expect VoiceErrors.VALIDATION_FAILED
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import { describe, it, expect } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import { BEHAVIORAL_QUESTION_TYPE } from '@/server/data_structures/VoiceInteractionContext';
import type { SlotState, QuestionTypeDefinition } from '@/server/data_structures/VoiceInteractionContext';
import { MinimumSlotValidator } from '../MinimumSlotValidator';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

function createCompleteSlotState(): SlotState {
  return {
    slots: [
      { name: 'objective', value: 'Increase team velocity', confirmed: false },
      { name: 'actions', value: ['reorganized sprints', 'hired engineers', 'improved CI/CD'], confirmed: false },
      { name: 'obstacles', value: ['budget constraints'], confirmed: false },
      { name: 'outcome', value: '40% increase in delivery speed', confirmed: false },
      { name: 'roleClarity', value: 'Engineering manager for platform team', confirmed: false },
    ],
  };
}

function createPartialSlotState(omit: string[]): SlotState {
  const complete = createCompleteSlotState();
  return {
    slots: complete.slots.filter((s) => !omit.includes(s.name)),
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('MinimumSlotValidator.validate — Step 3: Validate minimum required slots', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return { valid: true } when all required slots are filled', () => {
      const slotState = createCompleteSlotState();

      const result = MinimumSlotValidator.validate(slotState, BEHAVIORAL_QUESTION_TYPE);

      expect(result).toBeDefined();
      expect(result.valid).toBe(true);
    });

    it('should return empty missing array when all slots present', () => {
      const slotState = createCompleteSlotState();

      const result = MinimumSlotValidator.validate(slotState, BEHAVIORAL_QUESTION_TYPE);

      expect(result.missing).toBeDefined();
      expect(result.missing).toHaveLength(0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object with valid boolean and missing string array', () => {
      const slotState = createCompleteSlotState();

      const result = MinimumSlotValidator.validate(slotState, BEHAVIORAL_QUESTION_TYPE);

      expect(typeof result.valid).toBe('boolean');
      expect(Array.isArray(result.missing)).toBe(true);
    });

    it('should return invalid result with missing slots listed', () => {
      const slotState = createPartialSlotState(['outcome', 'roleClarity']);

      const result = MinimumSlotValidator.validate(slotState, BEHAVIORAL_QUESTION_TYPE);

      expect(result.valid).toBe(false);
      expect(result.missing).toContain('outcome');
      expect(result.missing).toContain('roleClarity');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw VALIDATION_FAILED when outcome is missing', () => {
      const slotState = createPartialSlotState(['outcome']);

      try {
        MinimumSlotValidator.validateOrThrow(slotState, BEHAVIORAL_QUESTION_TYPE);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('VALIDATION_FAILED');
      }
    });

    it('should include missing slot name in error', () => {
      const slotState = createPartialSlotState(['outcome']);

      try {
        MinimumSlotValidator.validateOrThrow(slotState, BEHAVIORAL_QUESTION_TYPE);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).message).toContain('outcome');
      }
    });

    it('should treat empty string values as missing', () => {
      const slotState: SlotState = {
        slots: [
          { name: 'objective', value: '', confirmed: false },
          { name: 'actions', value: ['a', 'b', 'c'], confirmed: false },
          { name: 'obstacles', value: ['budget'], confirmed: false },
          { name: 'outcome', value: 'success', confirmed: false },
          { name: 'roleClarity', value: 'manager', confirmed: false },
        ],
      };

      const result = MinimumSlotValidator.validate(slotState, BEHAVIORAL_QUESTION_TYPE);

      expect(result.valid).toBe(false);
      expect(result.missing).toContain('objective');
    });

    it('should treat empty arrays as missing', () => {
      const slotState: SlotState = {
        slots: [
          { name: 'objective', value: 'increase velocity', confirmed: false },
          { name: 'actions', value: [], confirmed: false },
          { name: 'obstacles', value: ['budget'], confirmed: false },
          { name: 'outcome', value: 'success', confirmed: false },
          { name: 'roleClarity', value: 'manager', confirmed: false },
        ],
      };

      const result = MinimumSlotValidator.validate(slotState, BEHAVIORAL_QUESTION_TYPE);

      expect(result.valid).toBe(false);
      expect(result.missing).toContain('actions');
    });

    it('should throw when questionType is null', () => {
      try {
        MinimumSlotValidator.validate(
          createCompleteSlotState(),
          null as unknown as QuestionTypeDefinition,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('VALIDATION_FAILED');
      }
    });
  });
});
