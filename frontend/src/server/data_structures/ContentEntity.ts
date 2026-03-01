/**
 * ContentEntity - Zod schema and TypeScript types for the Content entity
 * with status field supporting review-to-approved transitions and
 * body field for content text edits.
 *
 * Resource: db-f8n5 (data_structure)
 * Paths:
 *   - 329-approve-reviewed-content-and-advance-workflow
 *   - 330-edit-content-by-voice-from-review-screen
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Content Status Enum
// ---------------------------------------------------------------------------

export const ContentStatus = {
  DRAFT: 'DRAFT',
  REVIEW: 'REVIEW',
  APPROVED: 'APPROVED',
  FINALIZE: 'FINALIZE',
} as const;

export type ContentStatus = (typeof ContentStatus)[keyof typeof ContentStatus];

// ---------------------------------------------------------------------------
// Workflow Stage Enum
// ---------------------------------------------------------------------------

export const WorkflowStage = {
  DRAFTING: 'DRAFTING',
  REVIEW: 'REVIEW',
  FINALIZE: 'FINALIZE',
  COMPLETE: 'COMPLETE',
} as const;

export type WorkflowStage = (typeof WorkflowStage)[keyof typeof WorkflowStage];

// ---------------------------------------------------------------------------
// Zod Schema
// ---------------------------------------------------------------------------

export const ContentEntitySchema = z.object({
  id: z.string().uuid(),
  body: z.string().optional(),
  status: z.enum(['DRAFT', 'REVIEW', 'APPROVED', 'FINALIZE']),
  workflowStage: z.enum(['DRAFTING', 'REVIEW', 'FINALIZE', 'COMPLETE']),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type ContentEntity = z.infer<typeof ContentEntitySchema>;

// ---------------------------------------------------------------------------
// Approval Result
// ---------------------------------------------------------------------------

export const ApprovalResultSchema = z.object({
  status: z.literal('APPROVED'),
  workflowStage: z.enum(['DRAFTING', 'REVIEW', 'FINALIZE', 'COMPLETE']),
});

export type ApprovalResult = z.infer<typeof ApprovalResultSchema>;
