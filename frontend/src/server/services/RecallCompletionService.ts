/**
 * RecallCompletionService - Orchestrates the recall completion flow:
 * capturing additional spoken input, transforming utterances into slot values,
 * merging with existing state, validating required slots, and confirming
 * completion to terminate the recall loop.
 *
 * Resource: db-h2s4 (service)
 * Path: 319-complete-required-slots-and-end-recall-loop
 */

import {
  StructuredSpokenInputEventSchema,
} from '@/server/data_structures/RecallSession';
import type {
  RecallSession,
  StructuredSpokenInputEvent,
  ValidationResult,
} from '@/server/data_structures/RecallSession';
import type { QuestionTypeDefinition } from '@/server/data_structures/VoiceInteractionContext';
import { RecallErrors } from '@/server/error_definitions/RecallErrors';
import { RequiredSlotVerifier } from '@/server/verifiers/RequiredSlotVerifier';
import { recallCompletionLogger } from '@/server/logging/recallCompletionLogger';

// ---------------------------------------------------------------------------
// Slot extraction patterns (deterministic — reuses patterns from SlotExtractor)
// ---------------------------------------------------------------------------

const SLOT_EXTRACTORS: Record<
  string,
  (utterance: string) => string | string[] | null
> = {
  objective(utterance: string): string | null {
    const patterns = [
      /(?:my )?(?:objective|goal|aim|purpose) (?:was|is) (?:to )?(.+?)(?:\.|$)/i,
      /(?:i )?(?:wanted|needed|tried) to (.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = utterance.match(pattern);
      if (match?.[1]) return match[1].trim();
    }
    return null;
  },

  actions(utterance: string): string[] | null {
    const patterns = [
      /(?:i )?(?:took|did|performed|made) (?:these |the following )?(?:actions?|steps?):?\s*(.+?)(?:\.|$)/i,
      /(?:actions?|steps?):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = utterance.match(pattern);
      if (match?.[1]) {
        const actions = match[1]
          .split(/,|;| and /)
          .map((a) => a.trim())
          .filter((a) => a.length > 0);
        if (actions.length > 0) return actions;
      }
    }
    return null;
  },

  obstacles(utterance: string): string[] | null {
    const patterns = [
      /(?:obstacle|challenge|difficulty|problem|issue)s? (?:was|were|included?):?\s*(.+?)(?:\.|$)/i,
      /(?:i )?(?:faced|encountered|dealt with):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = utterance.match(pattern);
      if (match?.[1]) {
        const obstacles = match[1]
          .split(/,|;| and /)
          .map((o) => o.trim())
          .filter((o) => o.length > 0);
        if (obstacles.length > 0) return obstacles;
      }
    }
    return null;
  },

  outcome(utterance: string): string | null {
    const patterns = [
      /(?:the )?(?:outcome|result|end result) (?:was|is):?\s*(.+?)(?:\.|$)/i,
      /(?:we |i )?(?:achieved|accomplished|delivered|resulted in):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = utterance.match(pattern);
      if (match?.[1]) return match[1].trim();
    }
    return null;
  },

  roleClarity(utterance: string): string | null {
    const patterns = [
      /(?:my )?(?:role|responsibility|position) (?:was|is):?\s*(.+?)(?:\.|$)/i,
      /(?:i was |i am )?(?:responsible for|in charge of|the lead on|leading):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = utterance.match(pattern);
      if (match?.[1]) return match[1].trim();
    }
    return null;
  },
};

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const RecallCompletionService = {
  // -------------------------------------------------------------------------
  // Step 1: Capture Additional Spoken Input
  // -------------------------------------------------------------------------

  /**
   * Accept spoken input and associate it with the active question_type
   * recall session.
   *
   * @param session - Active recall session (cfg-d2q3)
   * @param utterance - Raw spoken utterance from user
   * @returns StructuredSpokenInputEvent linked to the active session
   * @throws RecallError(INVALID_RECALL_STATE) if session is not active
   */
  captureAdditionalInput(
    session: RecallSession,
    utterance: string,
  ): StructuredSpokenInputEvent {
    // Validate session is active
    if (!session.active) {
      throw RecallErrors.INVALID_RECALL_STATE(
        'Cannot capture input — no active recall session exists',
      );
    }

    const event: StructuredSpokenInputEvent = {
      sessionId: session.sessionId,
      questionType: session.questionType.name,
      utterance,
    };

    // Validate against schema
    StructuredSpokenInputEventSchema.parse(event);

    recallCompletionLogger.info('Captured additional spoken input', {
      sessionId: session.sessionId,
      questionType: session.questionType.name,
    });

    return event;
  },

  // -------------------------------------------------------------------------
  // Step 2: Transform Utterance Into Slot Values
  // -------------------------------------------------------------------------

  /**
   * Convert the utterance into candidate slot-value pairs aligned with the
   * required slot definitions for the question_type.
   *
   * @param event - Structured spoken input event from Step 1
   * @param schema - Question type definition with slot schemas (cfg-f7s8)
   * @param session - Optional recall session for retry tracking
   * @returns Extracted slot-value pairs mapped to required slot identifiers
   * @throws RecallError(SLOT_PARSING_ERROR) if no recognizable slots found
   * @throws RecallError(INCOMPLETE_INFORMATION_ERROR) if retry limit exceeded
   */
  transformUtterance(
    event: StructuredSpokenInputEvent,
    schema: QuestionTypeDefinition,
    session?: RecallSession,
  ): Record<string, string | string[]> {
    const extracted: Record<string, string | string[]> = {};

    for (const slotDef of schema.slots) {
      const extractor = SLOT_EXTRACTORS[slotDef.name];

      if (extractor) {
        const value = extractor(event.utterance);
        if (value !== null) {
          extracted[slotDef.name] = value;
        }
      }
    }

    // Validate slot ids are from schema
    const validSlotNames = schema.slots.map((s) => s.name);
    for (const key of Object.keys(extracted)) {
      if (!validSlotNames.includes(key)) {
        delete extracted[key];
      }
    }

    // If no slots extracted → increment retry and throw
    if (Object.keys(extracted).length === 0) {
      if (session) {
        session.retryCount += 1;

        // Check if retry limit exceeded
        if (session.retryCount >= session.maxRetries) {
          throw RecallErrors.INCOMPLETE_INFORMATION_ERROR(
            `Maximum retry limit (${session.maxRetries}) exceeded — required slots remain unfilled`,
          );
        }
      }

      throw RecallErrors.SLOT_PARSING_ERROR(
        'Could not extract recognizable slot values from utterance',
      );
    }

    recallCompletionLogger.info('Transformed utterance into slot values', {
      sessionId: event.sessionId,
      extractedSlots: Object.keys(extracted),
    });

    return extracted;
  },

  // -------------------------------------------------------------------------
  // Step 3: Merge With Existing Recall State
  // -------------------------------------------------------------------------

  /**
   * Update the recall state by filling previously missing required slots
   * with newly extracted values.
   *
   * @param session - Recall session with existing partial slot state (cfg-d2q3)
   * @param extracted - Extracted slot-value pairs from Step 2
   * @throws RecallError(SLOT_VALIDATION_ERROR) if extracted keys don't match schema
   */
  mergeSlots(
    session: RecallSession,
    extracted: Record<string, string | string[]>,
  ): void {
    const validSlotNames = session.questionType.slots.map((s) => s.name);

    // Validate all extracted keys exist in schema
    for (const key of Object.keys(extracted)) {
      if (!validSlotNames.includes(key)) {
        throw RecallErrors.SLOT_VALIDATION_ERROR(
          `Slot identifier "${key}" does not match question type schema — valid slots: ${validSlotNames.join(', ')}`,
        );
      }
    }

    // Merge extracted values into slot state
    for (const [name, value] of Object.entries(extracted)) {
      const existingIndex = session.slotState.slots.findIndex((s) => s.name === name);

      if (existingIndex !== -1) {
        // Update existing slot
        session.slotState.slots[existingIndex] = {
          name,
          value,
          confirmed: false,
        };
      } else {
        // Add new slot
        session.slotState.slots.push({
          name,
          value,
          confirmed: false,
        });
      }
    }

    recallCompletionLogger.info('Merged extracted slots with existing state', {
      sessionId: session.sessionId,
      mergedSlots: Object.keys(extracted),
      totalFilledSlots: session.slotState.slots.length,
    });
  },

  // -------------------------------------------------------------------------
  // Step 4: Validate Required Slot Completion
  // -------------------------------------------------------------------------

  /**
   * Evaluate whether all required slots for the question_type are present
   * and valid.
   *
   * @param session - Recall session with updated slot state
   * @returns ValidationResult with `complete` boolean and optional `missingSlots`
   * @throws RecallError(SLOT_VALIDATION_ERROR) if slot constraints are violated
   */
  validateRequiredSlots(session: RecallSession): ValidationResult {
    return RequiredSlotVerifier.validate(session.slotState, session.questionType);
  },

  // -------------------------------------------------------------------------
  // Step 5: Confirm Completion And Terminate Recall Loop
  // -------------------------------------------------------------------------

  /**
   * Mark the recall loop as completed and generate a user-facing
   * confirmation message.
   *
   * @param session - Recall session to mark as complete
   * @param persistFn - Optional persistence callback (for testing error paths)
   * @returns Confirmation message string
   * @throws RecallError(RECALL_STATE_TRANSITION_ERROR) if state update fails
   */
  confirmCompletion(
    session: RecallSession,
    persistFn?: () => void,
  ): string {
    try {
      // Set session to inactive
      session.active = false;

      // Call persistence if provided (will throw on failure)
      if (persistFn) {
        persistFn();
      }

      const confirmation = `All required information for ${session.questionType.name} has been collected. The recall loop is now complete.`;

      recallCompletionLogger.info('Recall loop completed successfully', {
        sessionId: session.sessionId,
        questionType: session.questionType.name,
      });

      return confirmation;
    } catch (error) {
      // Log the error before rethrowing
      recallCompletionLogger.error(
        'Failed to update recall session state during completion',
        error,
        {
          sessionId: session.sessionId,
          questionType: session.questionType.name,
        },
      );

      // Reset active state since persistence failed
      session.active = true;

      throw RecallErrors.RECALL_STATE_TRANSITION_ERROR(
        `Failed to update recall session state during completion: ${error instanceof Error ? error.message : String(error)}`,
      );
    }
  },
} as const;
