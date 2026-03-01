/**
 * SlotValidationService - Evaluates whether submitted input fills any
 * of the currently missing required slots for the active question_type.
 *
 * Orchestrates RequiredSlotVerifier evaluation and returns a result
 * listing still-missing slots and newly satisfied slots.
 *
 * Resource: db-h2s4 (service)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { getRequiredSlotSchema } from '@/server/data_structures/RequiredSlotSchema';
import { SlotErrors } from '@/server/error_definitions/SlotErrors';
import { slotRepromptLogger } from '@/server/logging/slotRepromptLogger';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface SlotSubmissionPayload {
  sessionId: string;
  questionType: string;
  slotValues: Record<string, string>;
  attemptCount: number;
}

export interface SlotValidationResult {
  missingSlots: string[];
  newlySatisfied: string[];
}

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const SlotValidationService = {
  /**
   * Validate submitted slot values against the currently missing required slots.
   *
   * @param payload - Slot submission payload with sessionId, questionType, and slotValues
   * @param currentMissing - List of currently missing required slot names
   * @returns SlotValidationResult with missingSlots and newlySatisfied arrays
   * @throws SlotError(REQUIRED_SLOT_SCHEMA_ERROR) if question_type schema is not found
   */
  validate(
    payload: SlotSubmissionPayload,
    currentMissing: string[],
  ): SlotValidationResult {
    // Step 1: Look up the required slot schema for this question_type
    const schema = getRequiredSlotSchema(payload.questionType);

    if (!schema) {
      slotRepromptLogger.error(
        'Required slot schema not found for question type',
        undefined,
        {
          sessionId: payload.sessionId,
          questionType: payload.questionType,
        },
      );

      throw SlotErrors.REQUIRED_SLOT_SCHEMA_ERROR(
        `No required slot schema found for question type "${payload.questionType}"`,
      );
    }

    // Step 2: Evaluate each currently missing slot against submitted values
    const newlySatisfied: string[] = [];
    const stillMissing: string[] = [];

    for (const slotName of currentMissing) {
      const submittedValue = payload.slotValues[slotName];

      if (submittedValue !== undefined && submittedValue !== null) {
        // Check for non-empty (trim whitespace)
        const trimmed = typeof submittedValue === 'string' ? submittedValue.trim() : '';

        if (trimmed.length > 0) {
          newlySatisfied.push(slotName);
        } else {
          stillMissing.push(slotName);
        }
      } else {
        stillMissing.push(slotName);
      }
    }

    slotRepromptLogger.info('Slot validation completed', {
      sessionId: payload.sessionId,
      questionType: payload.questionType,
      totalMissing: currentMissing.length,
      newlySatisfied: newlySatisfied.length,
      stillMissing: stillMissing.length,
    });

    return {
      missingSlots: stillMissing,
      newlySatisfied,
    };
  },
} as const;
