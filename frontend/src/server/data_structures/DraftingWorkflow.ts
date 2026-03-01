/**
 * DraftingWorkflow - Zod schemas and TypeScript types for
 * the drafting workflow entity that tracks drafting readiness.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 * Maps to: drafting_workflows table
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Drafting Workflow Status
// ---------------------------------------------------------------------------

export const DraftingWorkflowStatus = {
  READY: 'Ready',
  ON_HOLD: 'On Hold',
  IN_PROGRESS: 'In Progress',
  COMPLETED: 'Completed',
} as const;

export type DraftingWorkflowStatus =
  (typeof DraftingWorkflowStatus)[keyof typeof DraftingWorkflowStatus];

// ---------------------------------------------------------------------------
// DraftingWorkflow Schema
// ---------------------------------------------------------------------------

export const DraftingWorkflowSchema = z.object({
  id: z.string().min(1),
  claimId: z.string().min(1),
  status: z.enum(['Ready', 'On Hold', 'In Progress', 'Completed']),
  reason: z.string().optional(),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type DraftingWorkflow = z.infer<typeof DraftingWorkflowSchema>;

// ---------------------------------------------------------------------------
// Claim Status Response — API response DTO for claim + drafting status
// ---------------------------------------------------------------------------

export const ClaimStatusResponseSchema = z.object({
  claimStatus: z.string().min(1),
  draftingStatus: z.string().min(1),
  timedOut: z.boolean().optional(),
});

export type ClaimStatusResponse = z.infer<typeof ClaimStatusResponseSchema>;
