/**
 * OrientStoryRecord - Zod schemas and TypeScript types for the orient story path.
 *
 * Defines: Experience, OrientEvent, OrientExecutionContext,
 *          StoryCreationPayload, and OrientStoryRecord.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 295-orient-state-creates-single-story-record
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Zod Schemas
// ---------------------------------------------------------------------------

export const ExperienceSchema = z.object({
  id: z.string().min(1, 'Experience id is required'),
  title: z.string().min(1, 'Experience title is required'),
  summary: z.string().min(1, 'Experience summary is required'),
});

export const OrientEventSchema = z.object({
  experiences: z.array(ExperienceSchema).min(1, 'At least one experience is required'),
});

export const OrientExecutionContextSchema = z.object({
  experiences: z.array(ExperienceSchema).min(1),
});

export const StoryCreationPayloadSchema = z.object({
  story_title: z.string().min(1, 'Story title is required'),
  initial_context: z.object({
    experienceId: z.string().min(1),
    summary: z.string().min(1),
  }),
});

export const OrientStoryRecordSchema = z.object({
  id: z.string().uuid().optional(),
  story_title: z.string().min(1, 'Story title is required'),
  initial_context: z.object({
    experienceId: z.string().min(1),
    summary: z.string().min(1),
  }),
  createdAt: z.string().optional(),
  updatedAt: z.string().optional(),
});

// ---------------------------------------------------------------------------
// TypeScript Types (inferred from Zod schemas)
// ---------------------------------------------------------------------------

export type Experience = z.infer<typeof ExperienceSchema>;
export type OrientEvent = z.infer<typeof OrientEventSchema>;
export type OrientExecutionContext = z.infer<typeof OrientExecutionContextSchema>;
export type StoryCreationPayload = z.infer<typeof StoryCreationPayloadSchema>;
export type OrientStoryRecord = z.infer<typeof OrientStoryRecordSchema>;
