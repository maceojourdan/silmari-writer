/**
 * DraftStoryRecord - Zod schemas and TypeScript types for the draft state path.
 *
 * Defines: Claim, DraftStoryRecord, DraftExecutionContext,
 *          FilteredClaimSet, DraftPayload, DraftResponse.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Claim — individual claim with type and truth_check metadata
// ---------------------------------------------------------------------------

export const ClaimSchema = z.object({
  id: z.string().min(1),
  text: z.string().min(1),
  type: z.enum(['hard', 'soft']),
  truth_check: z
    .object({
      status: z.enum(['confirmed', 'denied']).optional(),
      source: z.string().optional(),
    })
    .optional(),
});

export type Claim = z.infer<typeof ClaimSchema>;

// ---------------------------------------------------------------------------
// DraftStoryRecord — StoryRecord in DRAFT state with truth_checks
// ---------------------------------------------------------------------------

export const DraftStoryRecordSchema = z.object({
  id: z.string().min(1),
  status: z.enum(['DRAFT', 'APPROVED', 'FINALIZED']),
  truth_checks: z.array(ClaimSchema),
  draft_text: z.string().optional(),
  claims_used: z.array(z.string()).optional(),
});

export type DraftStoryRecord = z.infer<typeof DraftStoryRecordSchema>;

// ---------------------------------------------------------------------------
// DraftExecutionContext — returned by Step 1 (trigger)
// ---------------------------------------------------------------------------

export interface DraftExecutionContext {
  storyRecordId: string;
  storyRecord: DraftStoryRecord;
}

// ---------------------------------------------------------------------------
// FilteredClaimSet — returned by Step 3 (filter)
// ---------------------------------------------------------------------------

export type FilteredClaimSet = Claim[];

// ---------------------------------------------------------------------------
// DraftPayload — returned by Step 4 (generate)
// ---------------------------------------------------------------------------

export interface DraftPayload {
  draft_text: string;
  claims_used: string[];
}

// ---------------------------------------------------------------------------
// DraftResponse — returned by Step 6 (response)
// ---------------------------------------------------------------------------

export const DraftResponseSchema = z.object({
  draft_text: z.string(),
  claims_used: z.array(z.string()),
});

export type DraftResponse = z.infer<typeof DraftResponseSchema>;
