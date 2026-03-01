/**
 * RecallSession - Stores and manages the recall session lifecycle for
 * capturing additional spoken input and completing required slots for a
 * question_type.
 *
 * Resource: cfg-d2q3 (common_structure)
 * Path: 319-complete-required-slots-and-end-recall-loop
 *
 * Extends VoiceInteractionContext with active state tracking and a
 * key-value slot map for direct slot access during the completion flow.
 */

import { z } from 'zod';
import {
  QuestionTypeDefinitionSchema,
  SlotStateSchema,
} from './VoiceInteractionContext';
import type {
  QuestionTypeDefinition,
  SlotState,
  SlotValue,
} from './VoiceInteractionContext';

// ---------------------------------------------------------------------------
// Recall Session Schema
// ---------------------------------------------------------------------------

export const RecallSessionSchema = z.object({
  sessionId: z.string().uuid(),
  questionType: QuestionTypeDefinitionSchema,
  slotState: SlotStateSchema,
  active: z.boolean(),
  retryCount: z.number().int().min(0).default(0),
  maxRetries: z.number().int().min(1).default(3),
});

export type RecallSession = z.infer<typeof RecallSessionSchema>;

// ---------------------------------------------------------------------------
// Structured Spoken Input Event
// ---------------------------------------------------------------------------

export const StructuredSpokenInputEventSchema = z.object({
  sessionId: z.string().uuid(),
  questionType: z.string().min(1),
  utterance: z.string().min(1),
});

export type StructuredSpokenInputEvent = z.infer<typeof StructuredSpokenInputEventSchema>;

// ---------------------------------------------------------------------------
// Validation Result
// ---------------------------------------------------------------------------

export const ValidationResultSchema = z.object({
  complete: z.boolean(),
  missingSlots: z.array(z.string()).optional(),
});

export type ValidationResult = z.infer<typeof ValidationResultSchema>;

// ---------------------------------------------------------------------------
// Helpers: Slot Map
// ---------------------------------------------------------------------------

/**
 * Convert a SlotState (array of SlotValue) into a simple key-value object.
 * Null values indicate unfilled slots.
 */
export function slotStateToMap(
  slotState: SlotState,
  questionType: QuestionTypeDefinition,
): Record<string, string | string[] | null> {
  const map: Record<string, string | string[] | null> = {};

  // Initialize all required slots as null
  for (const slotName of questionType.minimumRequiredSlots) {
    map[slotName] = null;
  }

  // Fill from slot state
  for (const slot of slotState.slots) {
    map[slot.name] = slot.value;
  }

  return map;
}

/**
 * Convert a key-value slot map back into a SlotState array.
 */
export function mapToSlotState(
  slotMap: Record<string, string | string[] | null>,
): SlotState {
  const slots: SlotValue[] = [];

  for (const [name, value] of Object.entries(slotMap)) {
    if (value !== null) {
      slots.push({ name, value, confirmed: false });
    }
  }

  return { slots };
}

// ---------------------------------------------------------------------------
// Default question type for recall completion (matching existing schema)
// ---------------------------------------------------------------------------

export const BEHAVIORAL_QUESTION_TYPE_RECALL: QuestionTypeDefinition = {
  name: 'behavioral_question',
  slots: [
    { name: 'objective', required: true, type: 'string' },
    { name: 'actions', required: true, type: 'string_array', minCount: 3 },
    { name: 'obstacles', required: true, type: 'string_array', minCount: 1 },
    { name: 'outcome', required: true, type: 'string' },
    { name: 'roleClarity', required: true, type: 'string' },
  ],
  minimumRequiredSlots: ['objective', 'actions', 'obstacles', 'outcome', 'roleClarity'],
};

// ---------------------------------------------------------------------------
// Factory: Create a new RecallSession
// ---------------------------------------------------------------------------

export function createRecallSession(
  sessionId: string,
  questionType: QuestionTypeDefinition,
  initialSlotState?: SlotState,
): RecallSession {
  return RecallSessionSchema.parse({
    sessionId,
    questionType,
    slotState: initialSlotState ?? { slots: [] },
    active: true,
    retryCount: 0,
    maxRetries: 3,
  });
}
