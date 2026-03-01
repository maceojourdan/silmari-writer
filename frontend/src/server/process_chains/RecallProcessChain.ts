/**
 * RecallProcessChain - Represents the workflow step sequencing that
 * must not advance when required slots remain unfilled.
 *
 * Coordinates between SlotValidationService and RecallWorkflowProcessor
 * to enforce the re-prompt loop.
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { SlotValidationService } from '@/server/services/SlotValidationService';
import type { SlotSubmissionPayload, SlotValidationResult } from '@/server/services/SlotValidationService';
import { RecallWorkflowProcessor } from '@/server/processors/RecallWorkflowProcessor';
import type { RecallWorkflowState } from '@/server/processors/RecallWorkflowProcessor';
import { slotRepromptLogger } from '@/server/logging/slotRepromptLogger';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface RecallProcessResult {
  state: RecallWorkflowState;
  validationResult: SlotValidationResult;
}

// ---------------------------------------------------------------------------
// Process Chain
// ---------------------------------------------------------------------------

export const RecallProcessChain = {
  /**
   * Execute the recall re-prompt process:
   * 1. Validate slot submission
   * 2. Enforce workflow guard (no progression with unfilled slots)
   * 3. Return updated state for re-prompt generation
   *
   * @param payload - Slot submission payload
   * @param currentState - Current recall workflow state
   * @returns RecallProcessResult with updated state and validation result
   */
  execute(
    payload: SlotSubmissionPayload,
    currentState: RecallWorkflowState,
  ): RecallProcessResult {
    slotRepromptLogger.info('RecallProcessChain executing', {
      sessionId: payload.sessionId,
      attemptCount: payload.attemptCount,
    });

    // Step 1: Validate slot submission against current missing slots
    const validationResult = SlotValidationService.validate(
      payload,
      currentState.missingSlots,
    );

    // Step 2: Apply workflow processor — prevents progression if needed
    const newState = RecallWorkflowProcessor.handleValidationResult(
      currentState,
      validationResult,
    );

    slotRepromptLogger.info('RecallProcessChain completed', {
      sessionId: payload.sessionId,
      stillMissing: newState.missingSlots.length,
      newlySatisfied: validationResult.newlySatisfied.length,
    });

    return {
      state: newState,
      validationResult,
    };
  },
} as const;
