/**
 * Draft - Zod schema and TypeScript types for the Draft entity
 * with status lifecycle: DRAFT → APPROVED → FINALIZED.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Draft Status Enum
// ---------------------------------------------------------------------------

export const DraftStatus = {
  DRAFT: 'DRAFT',
  APPROVED: 'APPROVED',
  FINALIZED: 'FINALIZED',
} as const;

export type DraftStatus = (typeof DraftStatus)[keyof typeof DraftStatus];

// ---------------------------------------------------------------------------
// Interaction Data — captures user interaction history for metrics
// ---------------------------------------------------------------------------

export const InteractionDataSchema = z.object({
  editsCount: z.number().int().min(0),
  revisionsCount: z.number().int().min(0),
  claimsVerified: z.number().int().min(0),
  totalClaims: z.number().int().min(0),
  signalEvents: z.number().int().min(0),
});

export type InteractionData = z.infer<typeof InteractionDataSchema>;

// ---------------------------------------------------------------------------
// Draft Zod Schema
// ---------------------------------------------------------------------------

export const DraftSchema = z.object({
  id: z.string().min(1),
  status: z.enum(['DRAFT', 'APPROVED', 'FINALIZED']),
  content: z.string(),
  title: z.string().optional(),
  userId: z.string().min(1),
  createdAt: z.string(),
  updatedAt: z.string(),
  approvedAt: z.string().optional(),
  finalizedAt: z.string().optional(),
  interactionData: InteractionDataSchema.optional(),
});

export type Draft = z.infer<typeof DraftSchema>;

// ---------------------------------------------------------------------------
// Export Artifact — produced when a draft is finalized
// ---------------------------------------------------------------------------

export const ExportArtifactSchema = z.object({
  draftId: z.string().min(1),
  content: z.string(),
  title: z.string().optional(),
  exportedAt: z.string(),
  format: z.enum(['text', 'markdown', 'html']).default('text'),
  metadata: z.object({
    userId: z.string().min(1),
    originalCreatedAt: z.string(),
    finalizedAt: z.string(),
  }),
});

export type ExportArtifact = z.infer<typeof ExportArtifactSchema>;

// ---------------------------------------------------------------------------
// Finalize Metrics — computed during finalization
// ---------------------------------------------------------------------------

export const FinalizeMetricsSchema = z.object({
  timeToDraft: z.number(),
  confirmationRate: z.number(),
  signalDensity: z.number(),
});

export type FinalizeMetrics = z.infer<typeof FinalizeMetricsSchema>;
