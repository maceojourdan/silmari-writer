/**
 * RequiredSlotVerifier - Validates that all required slots for a question_type
 * are present, non-empty, and conform to slot-level constraints.
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 319-complete-required-slots-and-end-recall-loop
 *
 * Combines presence checks (all required slots filled) with constraint
 * validation (e.g., minCount for array slots) to produce a typed
 * ValidationResult.
 */

import type {
  QuestionTypeDefinition,
  SlotState,
  SlotDefinition,
} from '@/server/data_structures/VoiceInteractionContext';
import type { ValidationResult } from '@/server/data_structures/RecallSession';
import { RecallErrors } from '@/server/error_definitions/RecallErrors';

// ---------------------------------------------------------------------------
// RequiredSlotVerifier
// ---------------------------------------------------------------------------

export const RequiredSlotVerifier = {
  /**
   * Validate that all required slots are present and constraints are satisfied.
   *
   * @param slotState - Current slot state to validate
   * @param questionType - Question type definition with slot schemas and required slots
   * @returns ValidationResult with `complete` boolean and optional `missingSlots`
   * @throws RecallError(SLOT_VALIDATION_ERROR) if a filled slot violates its constraints
   */
  validate(
    slotState: SlotState,
    questionType: QuestionTypeDefinition,
  ): ValidationResult {
    if (!questionType || !questionType.minimumRequiredSlots) {
      throw RecallErrors.SLOT_VALIDATION_ERROR(
        'Cannot validate slots without question type definition',
      );
    }

    const missingSlots: string[] = [];

    for (const requiredSlotName of questionType.minimumRequiredSlots) {
      const filledSlot = slotState.slots.find((s) => s.name === requiredSlotName);

      if (!filledSlot) {
        missingSlots.push(requiredSlotName);
        continue;
      }

      // Check non-empty
      if (typeof filledSlot.value === 'string' && filledSlot.value.trim() === '') {
        missingSlots.push(requiredSlotName);
        continue;
      }

      if (Array.isArray(filledSlot.value) && filledSlot.value.length === 0) {
        missingSlots.push(requiredSlotName);
        continue;
      }

      // Check constraint satisfaction (e.g., minCount for arrays)
      const definition = questionType.slots.find(
        (s: SlotDefinition) => s.name === requiredSlotName,
      );

      if (definition && definition.type === 'string_array' && definition.minCount) {
        if (!Array.isArray(filledSlot.value)) {
          throw RecallErrors.SLOT_VALIDATION_ERROR(
            `Slot "${requiredSlotName}" expected array value but got string`,
          );
        }

        const validItems = filledSlot.value.filter(
          (v) => typeof v === 'string' && v.trim() !== '',
        );

        if (validItems.length < definition.minCount) {
          throw RecallErrors.SLOT_VALIDATION_ERROR(
            `Slot "${requiredSlotName}" requires at least ${definition.minCount} items (got ${validItems.length})`,
          );
        }
      }
    }

    return {
      complete: missingSlots.length === 0,
      missingSlots: missingSlots.length > 0 ? missingSlots : undefined,
    };
  },
} as const;
