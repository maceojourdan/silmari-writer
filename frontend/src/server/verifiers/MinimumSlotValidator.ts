/**
 * MinimumSlotValidator - Validates that all minimum required slots
 * for a question_type are present and non-empty.
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 318-complete-voice-answer-advances-workflow
 *
 * Returns a structured result with { valid, missing } or throws
 * VoiceErrors.VALIDATION_FAILED when used in throw mode.
 */

import type {
  SlotState,
  QuestionTypeDefinition,
} from '@/server/data_structures/VoiceInteractionContext';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';

// ---------------------------------------------------------------------------
// Validation Result
// ---------------------------------------------------------------------------

export interface MinimumSlotValidationResult {
  valid: boolean;
  missing: string[];
}

// ---------------------------------------------------------------------------
// MinimumSlotValidator
// ---------------------------------------------------------------------------

export const MinimumSlotValidator = {
  /**
   * Evaluate whether all minimum required slots are present and valid.
   *
   * @param slotState - Current slot state to validate
   * @param questionType - Question type definition with minimumRequiredSlots
   * @returns { valid: boolean, missing: string[] }
   * @throws VoiceError(VALIDATION_FAILED) if questionType is null/invalid
   */
  validate(
    slotState: SlotState,
    questionType: QuestionTypeDefinition,
  ): MinimumSlotValidationResult {
    if (!questionType || !questionType.minimumRequiredSlots) {
      throw VoiceErrors.VALIDATION_FAILED(
        'Cannot validate slots without question type definition',
      );
    }

    const filledSlotNames = slotState.slots
      .filter((s) => {
        if (typeof s.value === 'string') return s.value.trim() !== '';
        if (Array.isArray(s.value)) return s.value.length > 0;
        return false;
      })
      .map((s) => s.name);

    const missing = questionType.minimumRequiredSlots.filter(
      (name) => !filledSlotNames.includes(name),
    );

    return {
      valid: missing.length === 0,
      missing,
    };
  },

  /**
   * Same as validate but throws VoiceErrors.VALIDATION_FAILED if
   * any required slots are missing.
   *
   * @throws VoiceError(VALIDATION_FAILED) if validation fails
   */
  validateOrThrow(
    slotState: SlotState,
    questionType: QuestionTypeDefinition,
  ): MinimumSlotValidationResult {
    const result = this.validate(slotState, questionType);

    if (!result.valid) {
      throw VoiceErrors.VALIDATION_FAILED(
        `Missing required slots: ${result.missing.join(', ')}`,
      );
    }

    return result;
  },
} as const;
