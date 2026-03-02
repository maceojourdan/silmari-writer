/**
 * Onboarding - Zod schema and TypeScript types for the Onboarding entity.
 *
 * Represents a user's onboarding progress with step completion tracking.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Onboarding Status Enum
// ---------------------------------------------------------------------------

export const OnboardingStatus = {
  NOT_STARTED: 'NOT_STARTED',
  IN_PROGRESS: 'IN_PROGRESS',
  COMPLETED: 'COMPLETED',
} as const;

export type OnboardingStatus =
  (typeof OnboardingStatus)[keyof typeof OnboardingStatus];

// ---------------------------------------------------------------------------
// Zod Schemas
// ---------------------------------------------------------------------------

export const OnboardingSchema = z.object({
  id: z.string().uuid(),
  userId: z.string().min(1),
  step: z.number().int().min(1),
  status: z.enum(['NOT_STARTED', 'IN_PROGRESS', 'COMPLETED']),
  completedAt: z.string().nullable(),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type Onboarding = z.infer<typeof OnboardingSchema>;

// ---------------------------------------------------------------------------
// Completion Result (Step 3 output)
// ---------------------------------------------------------------------------

export const OnboardingCompletionResultSchema = z.object({
  id: z.string().uuid(),
  userId: z.string().min(1),
  step: z.number().int().min(1),
  status: z.literal('COMPLETED'),
  completedAt: z.string(),
});

export type OnboardingCompletionResult = z.infer<
  typeof OnboardingCompletionResultSchema
>;

// ---------------------------------------------------------------------------
// Complete Onboarding Step Request (frontend → backend)
// ---------------------------------------------------------------------------

export const CompleteOnboardingStepRequestSchema = z.object({
  userId: z.string().min(1),
  step: z.number().int().min(1),
  metadata: z.record(z.string(), z.any()).optional(),
});

export type CompleteOnboardingStepRequest = z.infer<
  typeof CompleteOnboardingStepRequestSchema
>;

// ---------------------------------------------------------------------------
// Complete Onboarding Step Response (backend → frontend)
// ---------------------------------------------------------------------------

export const CompleteOnboardingStepResponseSchema = z.object({
  status: z.literal('completed'),
  onboardingId: z.string().uuid(),
  step: z.number().int().min(1),
  analyticsRecorded: z.boolean(),
});

export type CompleteOnboardingStepResponse = z.infer<
  typeof CompleteOnboardingStepResponseSchema
>;
