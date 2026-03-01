/**
 * Claimant - Zod schemas and TypeScript types for claimant profiles
 * used in the verification workflow.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 323-fail-verification-when-no-contact-method
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Claimant Key Claim (summary)
// ---------------------------------------------------------------------------

export const ClaimantKeyClaimSchema = z.object({
  id: z.string().min(1),
  category: z.string().min(1),
  content: z.string().min(1),
});

export type ClaimantKeyClaim = z.infer<typeof ClaimantKeyClaimSchema>;

// ---------------------------------------------------------------------------
// Claimant Schema
// ---------------------------------------------------------------------------

export const ClaimantSchema = z.object({
  id: z.string().min(1),
  keyClaims: z.array(ClaimantKeyClaimSchema),
  phone: z.string().nullable(),
  smsOptIn: z.boolean(),
});

export type Claimant = z.infer<typeof ClaimantSchema>;
