/**
 * VerificationAttempt - Zod schemas and TypeScript types for
 * verification attempt records tracking pass/fail outcomes.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 323-fail-verification-when-no-contact-method
 * Maps to: verification_attempts table
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Verification Attempt Status
// ---------------------------------------------------------------------------

export const VerificationAttemptStatus = {
  FAILED: 'FAILED',
  PENDING: 'PENDING',
  PASSED: 'PASSED',
} as const;

export type VerificationAttemptStatus =
  (typeof VerificationAttemptStatus)[keyof typeof VerificationAttemptStatus];

// ---------------------------------------------------------------------------
// Verification Failure Reason
// ---------------------------------------------------------------------------

export const VerificationFailureReason = {
  MISSING_CONTACT_METHOD: 'MISSING_CONTACT_METHOD',
  DISPUTED: 'DISPUTED',
  TIMEOUT: 'TIMEOUT',
} as const;

export type VerificationFailureReason =
  (typeof VerificationFailureReason)[keyof typeof VerificationFailureReason];

// ---------------------------------------------------------------------------
// Drafting Status
// ---------------------------------------------------------------------------

export const DraftingStatus = {
  ALLOWED: 'ALLOWED',
  BLOCKED: 'BLOCKED',
  IN_PROGRESS: 'IN_PROGRESS',
} as const;

export type DraftingStatus =
  (typeof DraftingStatus)[keyof typeof DraftingStatus];

// ---------------------------------------------------------------------------
// VerificationAttempt Schema
// ---------------------------------------------------------------------------

export const VerificationAttemptSchema = z.object({
  id: z.string().min(1),
  claimantId: z.string().min(1),
  status: z.enum(['FAILED', 'PENDING', 'PASSED']),
  reason: z.string().optional(),
  draftingStatus: z.enum(['ALLOWED', 'BLOCKED', 'IN_PROGRESS']).optional(),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type VerificationAttempt = z.infer<typeof VerificationAttemptSchema>;

// ---------------------------------------------------------------------------
// Initiate Verification Request / Response
// ---------------------------------------------------------------------------

export const InitiateVerificationRequestSchema = z.object({
  claimantId: z.string().uuid(),
});

export type InitiateVerificationRequest = z.infer<typeof InitiateVerificationRequestSchema>;

export const InitiateVerificationResponseSchema = z.object({
  verificationStatus: z.enum(['FAILED', 'PENDING']),
  reason: z.string().optional(),
  draftingAllowed: z.boolean(),
});

export type InitiateVerificationResponse = z.infer<typeof InitiateVerificationResponseSchema>;

// ---------------------------------------------------------------------------
// Start Drafting Result
// ---------------------------------------------------------------------------

export const StartDraftingResultSchema = z.object({
  draftingAllowed: z.boolean(),
  reason: z.string().optional(),
});

export type StartDraftingResult = z.infer<typeof StartDraftingResultSchema>;
