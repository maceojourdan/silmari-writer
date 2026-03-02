/**
 * FinalizeCompletion - Zod schemas and TypeScript types for the
 * finalize-answer-without-sms-follow-up workflow.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// FinalizeCompletionContext — input from the process chain
// ---------------------------------------------------------------------------

export const FinalizeCompletionContextSchema = z.object({
  answerId: z.string().min(1),
});

export type FinalizeCompletionContext = z.infer<typeof FinalizeCompletionContextSchema>;

// ---------------------------------------------------------------------------
// AnswerWithUserPreference — enriched entity from Step 2
// ---------------------------------------------------------------------------

export const AnswerWithUserPreferenceSchema = z.object({
  id: z.string().uuid(),
  status: z.enum(['DRAFT', 'COMPLETED', 'FINALIZED']),
  user: z.object({
    smsOptIn: z.boolean(),
  }),
});

export type AnswerWithUserPreference = z.infer<typeof AnswerWithUserPreferenceSchema>;

// ---------------------------------------------------------------------------
// EligibilityDecision — output from the verifier (Step 3)
// ---------------------------------------------------------------------------

export const EligibilityDecisionSchema = z.object({
  eligible: z.boolean(),
});

export type EligibilityDecision = z.infer<typeof EligibilityDecisionSchema>;

// ---------------------------------------------------------------------------
// PostFinalizeResult — output from SMS decision (Step 4)
// ---------------------------------------------------------------------------

export const PostFinalizeResultSchema = z.object({
  smsDispatched: z.boolean(),
});

export type PostFinalizeResult = z.infer<typeof PostFinalizeResultSchema>;

// ---------------------------------------------------------------------------
// FinalizeWorkflowResult — output from the process chain (Step 5)
// ---------------------------------------------------------------------------

export const FinalizeWorkflowResultSchema = z.object({
  success: z.boolean(),
});

export type FinalizeWorkflowResult = z.infer<typeof FinalizeWorkflowResultSchema>;
