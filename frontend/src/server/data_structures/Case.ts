/**
 * Case - Zod schema and TypeScript types for the Case entity,
 * which tracks the overall state of a claimant's case including
 * drafting status.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 322-handle-disputed-claims-and-block-drafting
 * Maps to: cases table
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Drafting Status Enum
// ---------------------------------------------------------------------------

export const DraftingStatus = {
  DRAFTING_ALLOWED: 'drafting_allowed',
  BLOCKED_DUE_TO_UNVERIFIED_CLAIMS: 'blocked_due_to_unverified_claims',
} as const;

export type DraftingStatus = (typeof DraftingStatus)[keyof typeof DraftingStatus];

// ---------------------------------------------------------------------------
// Case Schema
// ---------------------------------------------------------------------------

export const CaseSchema = z.object({
  id: z.string().min(1),
  claimantId: z.string().min(1),
  sessionId: z.string().min(1),
  drafting_status: z.enum(['drafting_allowed', 'blocked_due_to_unverified_claims']),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type Case = z.infer<typeof CaseSchema>;

// ---------------------------------------------------------------------------
// Case State Response (for frontend API contract)
// ---------------------------------------------------------------------------

export const CaseStateResponseSchema = z.object({
  caseId: z.string().min(1),
  drafting_status: z.enum(['drafting_allowed', 'blocked_due_to_unverified_claims']),
  blocked: z.boolean(),
  message: z.string().optional(),
});

export type CaseStateResponse = z.infer<typeof CaseStateResponseSchema>;
