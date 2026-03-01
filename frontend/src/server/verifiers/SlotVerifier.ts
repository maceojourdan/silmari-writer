/**
 * SlotVerifier - Validates slot values against their definitions and
 * enforces type/minimum constraints.
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import type { SlotDefinition, SlotValue } from '@/server/data_structures/VoiceInteractionContext';

// ---------------------------------------------------------------------------
// Validation result
// ---------------------------------------------------------------------------

export interface SlotValidationResult {
  valid: boolean;
  errors: Record<string, string>;
}

// ---------------------------------------------------------------------------
// SlotVerifier
// ---------------------------------------------------------------------------

export const SlotVerifier = {
  /**
   * Validate a single slot value against its definition.
   *
   * @throws SlotValidationError from VoiceErrors if value violates constraints.
   */
  validateSlotValue(
    slotValue: SlotValue,
    definition: SlotDefinition,
  ): SlotValidationResult {
    const errors: Record<string, string> = {};

    // Type check
    if (definition.type === 'string') {
      if (typeof slotValue.value !== 'string') {
        errors[slotValue.name] = `Expected string value for slot "${slotValue.name}"`;
      } else if (slotValue.value.trim() === '') {
        errors[slotValue.name] = `Slot "${slotValue.name}" must not be empty`;
      }
    } else if (definition.type === 'string_array') {
      if (!Array.isArray(slotValue.value)) {
        errors[slotValue.name] = `Expected array value for slot "${slotValue.name}"`;
      } else {
        const validItems = slotValue.value.filter(
          (v) => typeof v === 'string' && v.trim() !== '',
        );
        if (definition.minCount && validItems.length < definition.minCount) {
          errors[slotValue.name] =
            `Slot "${slotValue.name}" requires at least ${definition.minCount} items (got ${validItems.length})`;
        }
      }
    }

    return {
      valid: Object.keys(errors).length === 0,
      errors,
    };
  },

  /**
   * Validate all slot values against their definitions.
   */
  validateAll(
    slotValues: SlotValue[],
    definitions: SlotDefinition[],
  ): SlotValidationResult {
    const allErrors: Record<string, string> = {};

    for (const slotValue of slotValues) {
      const def = definitions.find((d) => d.name === slotValue.name);
      if (!def) {
        allErrors[slotValue.name] = `Unknown slot: "${slotValue.name}"`;
        continue;
      }

      const result = this.validateSlotValue(slotValue, def);
      if (!result.valid) {
        Object.assign(allErrors, result.errors);
      }
    }

    return {
      valid: Object.keys(allErrors).length === 0,
      errors: allErrors,
    };
  },
} as const;
