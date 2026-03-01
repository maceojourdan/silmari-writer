/**
 * SubmitSlotsHandler - Validates slot submission payload, delegates to
 * SlotValidationService and RecallWorkflowProcessor, and generates
 * targeted re-prompt responses.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 320-re-prompt-unfilled-required-slots
 *
 * Flow:
 * 1. Validate payload via Zod schema
 * 2. Run slot validation via RecallProcessChain
 * 3. Generate re-prompt with missing slot labels
 * 4. Include guidance hint after 5 attempts
 */

import { SubmitSlotsRequestSchema } from '@/api_contracts/submitSlots';
import type { SubmitSlotsResponse, SlotPrompt } from '@/api_contracts/submitSlots';
import { RecallProcessChain } from '@/server/process_chains/RecallProcessChain';
import type { RecallWorkflowState } from '@/server/processors/RecallWorkflowProcessor';
import { getRequiredSlotSchema } from '@/server/data_structures/RequiredSlotSchema';
import { SlotErrors, SlotError } from '@/server/error_definitions/SlotErrors';
import { slotRepromptLogger } from '@/server/logging/slotRepromptLogger';

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const GUIDANCE_HINT_THRESHOLD = 5;

// ---------------------------------------------------------------------------
// Handler
// ---------------------------------------------------------------------------

export const SubmitSlotsHandler = {
  /**
   * Handle the slot submission flow:
   * 1. Validate payload via Zod schema
   * 2. Run validation + workflow guard via RecallProcessChain
   * 3. Generate re-prompt response with missing slot labels
   *
   * @param rawPayload - Raw input with sessionId, questionType, slotValues, attemptCount
   * @returns SubmitSlotsResponse with prompts, attemptCount, and guidanceHint
   * @throws SlotError(SLOT_SUBMISSION_INVALID) on invalid payload
   * @throws SlotError(REQUIRED_SLOT_SCHEMA_ERROR) on unknown question type
   * @throws SlotError(RECOVERABLE_SLOT_RETRIEVAL_ERROR) on prompt generation failure
   */
  async handle(rawPayload: unknown): Promise<SubmitSlotsResponse> {
    // Step 1: Validate payload
    const validation = SubmitSlotsRequestSchema.safeParse(rawPayload);
    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');

      throw SlotErrors.SLOT_SUBMISSION_INVALID(
        `Invalid slot submission payload: ${details}`,
      );
    }

    const payload = validation.data;

    // Step 2: Look up schema to get current missing slots
    const schema = getRequiredSlotSchema(payload.questionType);
    if (!schema) {
      throw SlotErrors.REQUIRED_SLOT_SCHEMA_ERROR(
        `No required slot schema found for question type "${payload.questionType}"`,
      );
    }

    // Determine current missing slots based on what's NOT in slotValues
    // (or has empty values)
    const currentMissing = schema.requiredSlotNames.filter((name) => {
      const value = payload.slotValues[name];
      return !value || (typeof value === 'string' && value.trim() === '');
    });

    // Build initial workflow state
    const currentState: RecallWorkflowState = {
      sessionId: payload.sessionId,
      currentStep: 'RECALL',
      missingSlots: currentMissing.length > 0 ? currentMissing : schema.requiredSlotNames,
      attemptCount: payload.attemptCount,
    };

    // Step 3: Execute the recall process chain
    try {
      const processResult = RecallProcessChain.execute(
        {
          sessionId: payload.sessionId,
          questionType: payload.questionType,
          slotValues: payload.slotValues,
          attemptCount: payload.attemptCount,
        },
        currentState,
      );

      // Step 4: Generate prompts from missing slots
      const prompts = this.generatePrompts(
        processResult.state.missingSlots,
        schema.slots,
      );

      const newAttemptCount = processResult.state.attemptCount;
      const guidanceHint = newAttemptCount >= GUIDANCE_HINT_THRESHOLD;

      slotRepromptLogger.info('Re-prompt response generated', {
        sessionId: payload.sessionId,
        promptCount: prompts.length,
        attemptCount: newAttemptCount,
        guidanceHint,
      });

      return {
        prompts,
        attemptCount: newAttemptCount,
        guidanceHint,
      };
    } catch (error) {
      // Known slot errors → rethrow
      if (error instanceof SlotError) {
        throw error;
      }

      // Unknown errors → wrap as recoverable
      slotRepromptLogger.error(
        'Unexpected error during slot submission handling',
        error,
        { sessionId: payload.sessionId },
      );

      throw SlotErrors.RECOVERABLE_SLOT_RETRIEVAL_ERROR(
        `Failed to process slot submission: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },

  /**
   * Generate prompt objects from the list of missing slot names
   * using the slot schema definitions.
   *
   * @param missingSlots - Array of missing slot names
   * @param schemaSlots - Array of slot definitions from the schema
   * @returns Array of SlotPrompt objects with name and promptLabel
   */
  generatePrompts(
    missingSlots: string[],
    schemaSlots: Array<{ name: string; promptLabel: string }>,
  ): SlotPrompt[] {
    return missingSlots.map((slotName) => {
      const definition = schemaSlots.find((s) => s.name === slotName);
      return {
        name: slotName,
        promptLabel: definition?.promptLabel ?? `Please provide: ${slotName}`,
      };
    });
  },
} as const;
