/**
 * VoiceInteractionContext - Zod schemas and TypeScript types for voice
 * interaction context, slot state, and partial slot data used in the
 * recall voice loop.
 *
 * Resource: cfg-d2q3 (common_structure)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Slot definitions per question_type
// ---------------------------------------------------------------------------

export const SlotDefinitionSchema = z.object({
  name: z.string().min(1),
  required: z.boolean(),
  type: z.enum(['string', 'string_array']),
  /** Minimum count for array types (e.g., actions >= 3) */
  minCount: z.number().int().min(1).optional(),
});

export type SlotDefinition = z.infer<typeof SlotDefinitionSchema>;

// ---------------------------------------------------------------------------
// Question Type Definition — defines which slots exist and minimum requirements
// ---------------------------------------------------------------------------

export const QuestionTypeDefinitionSchema = z.object({
  name: z.string().min(1),
  slots: z.array(SlotDefinitionSchema).min(1),
  minimumRequiredSlots: z.array(z.string().min(1)).min(1),
});

export type QuestionTypeDefinition = z.infer<typeof QuestionTypeDefinitionSchema>;

// ---------------------------------------------------------------------------
// Individual slot value — a single filled slot
// ---------------------------------------------------------------------------

export const SlotValueSchema = z.object({
  name: z.string().min(1),
  value: z.union([z.string(), z.array(z.string())]),
  confirmed: z.boolean().default(false),
});

export type SlotValue = z.infer<typeof SlotValueSchema>;

// ---------------------------------------------------------------------------
// Slot State — the full current state of all slots
// ---------------------------------------------------------------------------

export const SlotStateSchema = z.object({
  slots: z.array(SlotValueSchema),
});

export type SlotState = z.infer<typeof SlotStateSchema>;

// ---------------------------------------------------------------------------
// Partial Slot Data — extracted from a single voice answer
// ---------------------------------------------------------------------------

export const PartialSlotDataSchema = z.object({
  slots: z.array(
    z.object({
      name: z.string().min(1),
      value: z.union([z.string().min(1), z.array(z.string().min(1)).min(1)]),
    }),
  ).min(1),
});

export type PartialSlotData = z.infer<typeof PartialSlotDataSchema>;

// ---------------------------------------------------------------------------
// Voice Interaction Context — full context for a voice recall interaction
// ---------------------------------------------------------------------------

export const VoiceInteractionContextSchema = z.object({
  sessionId: z.string().uuid(),
  questionType: QuestionTypeDefinitionSchema,
  slotState: SlotStateSchema,
  retryCount: z.number().int().min(0).default(0),
  maxRetries: z.number().int().min(1).default(2),
});

export type VoiceInteractionContext = z.infer<typeof VoiceInteractionContextSchema>;

// ---------------------------------------------------------------------------
// Minimum Slot Validation Result
// ---------------------------------------------------------------------------

export const MinimumSlotValidationResultSchema = z.object({
  valid: z.boolean(),
  missingSlots: z.array(z.string()),
  filledSlots: z.array(z.string()),
});

export type MinimumSlotValidationResult = z.infer<typeof MinimumSlotValidationResultSchema>;

// ---------------------------------------------------------------------------
// Voice Delivery Result
// ---------------------------------------------------------------------------

export const VoiceDeliveryResultSchema = z.object({
  deliveryStatus: z.enum(['played', 'fallback_text', 'failed']),
  promptText: z.string().min(1),
  fallbackTextPrompt: z.string().optional(),
});

export type VoiceDeliveryResult = z.infer<typeof VoiceDeliveryResultSchema>;

// ---------------------------------------------------------------------------
// Default question type for behavioral questions (matching existing schema)
// ---------------------------------------------------------------------------

export const BEHAVIORAL_QUESTION_TYPE: QuestionTypeDefinition = {
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
