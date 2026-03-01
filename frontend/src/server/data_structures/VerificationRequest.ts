/**
 * VerificationRequest - Zod schemas and TypeScript types for
 * verification request records and confirmation results.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 321-verify-key-claims-via-voice-or-sms
 * Maps to: verification_requests table
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Verification Request Status
// ---------------------------------------------------------------------------

export const VerificationRequestStatus = {
  PENDING: 'pending',
  CONFIRMED: 'confirmed',
  FAILED: 'failed',
  TIMED_OUT: 'timed_out',
} as const;

export type VerificationRequestStatus =
  (typeof VerificationRequestStatus)[keyof typeof VerificationRequestStatus];

// ---------------------------------------------------------------------------
// VerificationRequest Schema
// ---------------------------------------------------------------------------

export const VerificationRequestSchema = z.object({
  id: z.string().min(1),
  sessionId: z.string().min(1),
  status: z.enum(['pending', 'confirmed', 'failed', 'timed_out']),
  attemptCount: z.number().int().min(0),
  token: z.string().min(1),
  claimIds: z.array(z.string().min(1)),
  contactPhone: z.string().min(1),
  contactMethod: z.enum(['sms', 'voice']),
  createdAt: z.string(),
  respondedAt: z.string().nullable().optional(),
  updatedAt: z.string(),
});

export type VerificationRequest = z.infer<typeof VerificationRequestSchema>;

// ---------------------------------------------------------------------------
// Delivery Attempt
// ---------------------------------------------------------------------------

export const DeliveryAttemptSchema = z.object({
  id: z.string().min(1),
  requestId: z.string().min(1),
  attemptNumber: z.number().int().min(1),
  status: z.enum(['success', 'failed']),
  externalId: z.string().optional(),
  errorMessage: z.string().optional(),
  createdAt: z.string(),
});

export type DeliveryAttempt = z.infer<typeof DeliveryAttemptSchema>;

// ---------------------------------------------------------------------------
// Confirmation Result
// ---------------------------------------------------------------------------

export const ConfirmationResultSchema = z.object({
  fullConfirmation: z.boolean(),
  confirmedClaimIds: z.array(z.string().min(1)),
  requestId: z.string().min(1),
});

export type ConfirmationResult = z.infer<typeof ConfirmationResultSchema>;

// ---------------------------------------------------------------------------
// Inbound Confirmation Payload
// ---------------------------------------------------------------------------

export const InboundConfirmationPayloadSchema = z.object({
  token: z.string().min(1),
  confirmedClaimIds: z.array(z.string().min(1)),
});

export type InboundConfirmationPayload = z.infer<typeof InboundConfirmationPayloadSchema>;
