/**
 * StoryStructures - Zod schemas and TypeScript types for claim set
 * entities and structured draft generation.
 *
 * Defines: StoryClaim, StructuredDraftSection, StructuredDraft
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { z } from 'zod';
import { DraftSectionSchema } from './DraftDocumentStructure';

// ---------------------------------------------------------------------------
// StoryClaim — a claim within a claim set, with section metadata
// ---------------------------------------------------------------------------

export const StoryClaimSchema = z.object({
  id: z.string().uuid(),
  claimSetId: z.string().uuid(),
  content: z.string().min(1),
  status: z.enum(['CONFIRMED', 'UNCONFIRMED', 'PENDING']),
  section: DraftSectionSchema,
  order: z.number().int().min(0),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type StoryClaim = z.infer<typeof StoryClaimSchema>;

// ---------------------------------------------------------------------------
// StructuredDraftSection — a section within the structured draft
// ---------------------------------------------------------------------------

export const StructuredDraftSectionSchema = z.object({
  sectionName: DraftSectionSchema,
  claims: z.array(StoryClaimSchema),
});

export type StructuredDraftSection = z.infer<typeof StructuredDraftSectionSchema>;

// ---------------------------------------------------------------------------
// StructuredDraft — the complete draft with ordered sections
// ---------------------------------------------------------------------------

export const StructuredDraftSchema = z.object({
  id: z.string().uuid(),
  claimSetId: z.string().uuid(),
  sections: z.array(StructuredDraftSectionSchema),
  createdAt: z.string(),
});

export type StructuredDraft = z.infer<typeof StructuredDraftSchema>;

// ---------------------------------------------------------------------------
// GenerateDraftRequest — input to the generate-draft endpoint
// ---------------------------------------------------------------------------

export const GenerateDraftRequestSchema = z.object({
  claimSetId: z.string().uuid(),
});

export type GenerateDraftRequest = z.infer<typeof GenerateDraftRequestSchema>;

// ---------------------------------------------------------------------------
// GenerateDraftResponse — output from the generate-draft endpoint
// ---------------------------------------------------------------------------

export const GenerateDraftResponseSchema = z.object({
  draft: StructuredDraftSchema,
});

export type GenerateDraftResponse = z.infer<typeof GenerateDraftResponseSchema>;
