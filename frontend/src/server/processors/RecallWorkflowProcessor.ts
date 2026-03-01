/**
 * RecallWorkflowProcessor - Enforces workflow progression rules when
 * required slots remain unfilled.
 *
 * When validation shows zero newly satisfied slots, the processor
 * prevents advancement and keeps the workflow in RECALL state.
 *
 * Resource: db-b7r2 (processor)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import type { SlotValidationResult } from '@/server/services/SlotValidationService';
import { SlotErrors } from '@/server/error_definitions/SlotErrors';
import { slotRepromptLogger } from '@/server/logging/slotRepromptLogger';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface RecallWorkflowState {
  sessionId: string;
  currentStep: 'RECALL';
  missingSlots: string[];
  attemptCount: number;
}

// ---------------------------------------------------------------------------
// Processor
// ---------------------------------------------------------------------------

export const RecallWorkflowProcessor = {
  /**
   * Handle a slot validation result and determine if the workflow
   * should progress or remain in RECALL state.
   *
   * If newlySatisfied.length === 0, do not call RecallProcessChain.advance().
   * Increments attempt count when no progress is made.
   *
   * @param state - Current recall workflow state
   * @param result - Slot validation result from SlotValidationService
   * @returns Updated RecallWorkflowState (unchanged step, updated missingSlots)
   */
  handleValidationResult(
    state: RecallWorkflowState,
    result: SlotValidationResult,
  ): RecallWorkflowState {
    // If no slots were newly satisfied, prevent progression
    if (result.newlySatisfied.length === 0) {
      slotRepromptLogger.info('No newly satisfied slots — workflow stays in RECALL', {
        sessionId: state.sessionId,
        missingSlots: result.missingSlots,
        attemptCount: state.attemptCount + 1,
      });

      return {
        sessionId: state.sessionId,
        currentStep: 'RECALL',
        missingSlots: result.missingSlots,
        attemptCount: state.attemptCount + 1,
      };
    }

    // Some slots were satisfied but workflow still stays in RECALL
    // because there are still missing slots
    slotRepromptLogger.info('Some slots satisfied but missing slots remain', {
      sessionId: state.sessionId,
      newlySatisfied: result.newlySatisfied,
      stillMissing: result.missingSlots,
      attemptCount: state.attemptCount + 1,
    });

    return {
      sessionId: state.sessionId,
      currentStep: 'RECALL',
      missingSlots: result.missingSlots,
      attemptCount: state.attemptCount + 1,
    };
  },

  /**
   * Guard: Attempt to advance the workflow past RECALL.
   *
   * Throws WORKFLOW_GUARD_VIOLATION if missingSlots is non-empty,
   * preventing any progression with unfilled required slots.
   *
   * @param state - Current recall workflow state
   * @throws SlotError(WORKFLOW_GUARD_VIOLATION) if slots remain unfilled
   */
  attemptAdvance(state: RecallWorkflowState): void {
    if (state.missingSlots.length > 0) {
      slotRepromptLogger.error(
        'Workflow guard violation — attempted advance with unfilled slots',
        undefined,
        {
          sessionId: state.sessionId,
          missingSlots: state.missingSlots,
        },
      );

      throw SlotErrors.WORKFLOW_GUARD_VIOLATION(
        `Cannot advance workflow — ${state.missingSlots.length} required slot(s) remain unfilled: ${state.missingSlots.join(', ')}`,
      );
    }

    slotRepromptLogger.info('Workflow guard passed — all slots satisfied', {
      sessionId: state.sessionId,
    });
  },
} as const;
