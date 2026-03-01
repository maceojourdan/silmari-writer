/**
 * ClaimRecord - Zod schemas and TypeScript types for key claim records
 * used in the verification workflow.
 *
 * Resource: db-f8n5 (data_structure)
 * Paths:
 *   - 321-verify-key-claims-via-voice-or-sms
 *   - 322-handle-disputed-claims-and-block-drafting
 * Maps to: claims table (extended for verification)
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Claim Category Enum
// ---------------------------------------------------------------------------

export const ClaimCategory = {
  METRICS: 'metrics',
  SCOPE: 'scope',
  PRODUCTION: 'production',
  SECURITY: 'security',
} as const;

export type ClaimCategory = (typeof ClaimCategory)[keyof typeof ClaimCategory];

export const REQUIRED_CLAIM_CATEGORIES: ClaimCategory[] = [
  ClaimCategory.METRICS,
  ClaimCategory.SCOPE,
  ClaimCategory.PRODUCTION,
  ClaimCategory.SECURITY,
];

// ---------------------------------------------------------------------------
// Claim Verification Status
// ---------------------------------------------------------------------------

export const ClaimVerificationStatus = {
  UNVERIFIED: 'unverified',
  VERIFIED: 'verified',
  NOT_VERIFIED: 'not_verified',
} as const;

export type ClaimVerificationStatus =
  (typeof ClaimVerificationStatus)[keyof typeof ClaimVerificationStatus];

// ---------------------------------------------------------------------------
// Contact Method
// ---------------------------------------------------------------------------

export const ContactMethod = {
  SMS: 'sms',
  VOICE: 'voice',
} as const;

export type ContactMethod = (typeof ContactMethod)[keyof typeof ContactMethod];

// ---------------------------------------------------------------------------
// ClaimRecord Schema
// ---------------------------------------------------------------------------

export const ClaimRecordSchema = z.object({
  id: z.string().min(1),
  sessionId: z.string().min(1),
  category: z.enum(['metrics', 'scope', 'production', 'security']),
  status: z.enum(['unverified', 'verified', 'not_verified']),
  contactPhone: z.string().optional(),
  contactMethod: z.enum(['sms', 'voice']).optional(),
  content: z.string().min(1),
  verifiedAt: z.string().nullable().optional(),
  disputedAt: z.string().nullable().optional(),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type ClaimRecord = z.infer<typeof ClaimRecordSchema>;

// ---------------------------------------------------------------------------
// Eligibility Result
// ---------------------------------------------------------------------------

export interface EligibilityResult {
  eligible: boolean;
  claims: ClaimRecord[];
}
