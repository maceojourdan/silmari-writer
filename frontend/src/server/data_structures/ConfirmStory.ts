/**
 * ConfirmStory - Zod schemas and TypeScript types for the confirm-aligned-story-selection path.
 *
 * Defines: Story, Question, JobRequirement, OrientStoryData,
 *          ConfirmStoryRequest, ConfirmStoryResponse, ValidationResult.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 313-confirm-aligned-story-selection
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Story status for the confirm path
// ---------------------------------------------------------------------------

export const StoryConfirmStatusSchema = z.enum([
  'AVAILABLE',
  'CONFIRMED',
  'EXCLUDED',
]);
export type StoryConfirmStatus = z.infer<typeof StoryConfirmStatusSchema>;

// ---------------------------------------------------------------------------
// Core entity schemas
// ---------------------------------------------------------------------------

export const QuestionSchema = z.object({
  id: z.string().min(1, 'Question id is required'),
  text: z.string().min(1, 'Question text is required'),
  category: z.string().optional(),
});

export const JobRequirementSchema = z.object({
  id: z.string().min(1, 'Job requirement id is required'),
  description: z.string().min(1, 'Job requirement description is required'),
  priority: z.enum(['REQUIRED', 'PREFERRED', 'NICE_TO_HAVE']).optional(),
});

export const StorySchema = z.object({
  id: z.string().min(1, 'Story id is required'),
  title: z.string().min(1, 'Story title is required'),
  summary: z.string().min(1, 'Story summary is required'),
  status: StoryConfirmStatusSchema.default('AVAILABLE'),
  questionId: z.string().min(1, 'Question id is required'),
});

// ---------------------------------------------------------------------------
// Orient story data (loaded for display)
// ---------------------------------------------------------------------------

export const OrientStoryDataSchema = z.object({
  question: QuestionSchema,
  jobRequirements: z.array(JobRequirementSchema).min(1, 'At least one job requirement is required'),
  stories: z.array(StorySchema).min(1, 'At least one story is required'),
});

// ---------------------------------------------------------------------------
// Confirm story request/response
// ---------------------------------------------------------------------------

export const ConfirmStoryRequestSchema = z.object({
  questionId: z.string().min(1, 'Question id is required'),
  storyId: z.string().min(1, 'Story id is required'),
});

export const ConfirmStoryResponseSchema = z.object({
  confirmedStoryId: z.string().min(1),
  status: z.literal('CONFIRMED'),
  story: StorySchema,
  excludedCount: z.number().int().nonnegative(),
});

// ---------------------------------------------------------------------------
// Validation result (from backend verifier)
// ---------------------------------------------------------------------------

export const ValidationResultSchema = z.discriminatedUnion('valid', [
  z.object({ valid: z.literal(true) }),
  z.object({ valid: z.literal(false), errors: z.array(z.string()).min(1) }),
]);

// ---------------------------------------------------------------------------
// TypeScript types (inferred from Zod schemas)
// ---------------------------------------------------------------------------

export type Question = z.infer<typeof QuestionSchema>;
export type JobRequirement = z.infer<typeof JobRequirementSchema>;
export type Story = z.infer<typeof StorySchema>;
export type OrientStoryData = z.infer<typeof OrientStoryDataSchema>;
export type ConfirmStoryRequest = z.infer<typeof ConfirmStoryRequestSchema>;
export type ConfirmStoryResponse = z.infer<typeof ConfirmStoryResponseSchema>;
export type ValidationResult = z.infer<typeof ValidationResultSchema>;
