/**
 * RequiredSlotSchema - Static required slots per question_type.
 *
 * Defines the required slot schemas and constraints that must be
 * satisfied before workflow progression is permitted.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Slot Requirement Definition
// ---------------------------------------------------------------------------

export const SlotRequirementSchema = z.object({
  name: z.string().min(1),
  required: z.boolean(),
  type: z.enum(['string', 'string_array']),
  minCount: z.number().int().min(1).optional(),
  promptLabel: z.string().min(1),
});

export type SlotRequirement = z.infer<typeof SlotRequirementSchema>;

// ---------------------------------------------------------------------------
// Required Slot Schema Definition — per question_type
// ---------------------------------------------------------------------------

export const RequiredSlotSchemaDefinitionSchema = z.object({
  questionType: z.string().min(1),
  slots: z.array(SlotRequirementSchema).min(1),
  requiredSlotNames: z.array(z.string().min(1)).min(1),
});

export type RequiredSlotSchemaDefinition = z.infer<typeof RequiredSlotSchemaDefinitionSchema>;

// ---------------------------------------------------------------------------
// Static schema registry — maps question_type to required slots
// ---------------------------------------------------------------------------

export const REQUIRED_SLOT_SCHEMAS: Record<string, RequiredSlotSchemaDefinition> = {
  behavioral_question: {
    questionType: 'behavioral_question',
    slots: [
      { name: 'objective', required: true, type: 'string', promptLabel: 'What was your objective or goal?' },
      { name: 'actions', required: true, type: 'string_array', minCount: 3, promptLabel: 'What specific actions did you take? (at least 3)' },
      { name: 'obstacles', required: true, type: 'string_array', minCount: 1, promptLabel: 'What obstacles or challenges did you face?' },
      { name: 'outcome', required: true, type: 'string', promptLabel: 'What was the outcome or result?' },
      { name: 'roleClarity', required: true, type: 'string', promptLabel: 'What was your specific role or responsibility?' },
    ],
    requiredSlotNames: ['objective', 'actions', 'obstacles', 'outcome', 'roleClarity'],
  },
} as const;

// ---------------------------------------------------------------------------
// Lookup helper
// ---------------------------------------------------------------------------

/**
 * Get the required slot schema for a given question_type.
 *
 * @param questionType - The question type name
 * @returns The schema definition, or undefined if not found
 */
export function getRequiredSlotSchema(
  questionType: string,
): RequiredSlotSchemaDefinition | undefined {
  return REQUIRED_SLOT_SCHEMAS[questionType];
}
