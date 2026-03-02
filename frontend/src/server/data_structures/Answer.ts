/**
 * Answer - Zod schema and TypeScript types for the Answer entity
 * with finalized and editable fields supporting finalize-locks-editing flow.
 *
 * Resource: db-f8n5 (data_structure)
 * Paths:
 *   - 333-finalize-answer-locks-editing
 *   - 334-export-or-copy-finalized-answer
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Answer Status Enum
// ---------------------------------------------------------------------------

export const AnswerStatus = {
  DRAFT: 'DRAFT',
  COMPLETED: 'COMPLETED',
  FINALIZED: 'FINALIZED',
} as const;

export type AnswerStatus = (typeof AnswerStatus)[keyof typeof AnswerStatus];

// ---------------------------------------------------------------------------
// Zod Schema
// ---------------------------------------------------------------------------

export const AnswerSchema = z.object({
  id: z.string().uuid(),
  status: z.enum(['DRAFT', 'COMPLETED', 'FINALIZED']),
  finalized: z.boolean(),
  editable: z.boolean(),
  locked: z.boolean().default(false), // Path 334: locked=true when finalized and export-ready
  content: z.string(),
  userId: z.string().min(1),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type Answer = z.infer<typeof AnswerSchema>;

// ---------------------------------------------------------------------------
// Finalize Answer Result (Path 333)
// ---------------------------------------------------------------------------

export const FinalizeAnswerResultSchema = z.object({
  id: z.string().uuid(),
  finalized: z.literal(true),
  editable: z.literal(false),
});

export type FinalizeAnswerResult = z.infer<typeof FinalizeAnswerResultSchema>;
