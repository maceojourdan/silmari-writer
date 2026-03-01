/**
 * smsDisputeWebhook - Validates and parses inbound SMS dispute webhook payloads.
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 322-handle-disputed-claims-and-block-drafting
 *
 * Defines the Zod schema for the dispute webhook body and validates
 * that the token corresponds to an active verification request.
 *
 * On success: returns structured dispute data { claimantId, disputedClaimIds }.
 * On failure: throws DisputeError (MALFORMED_WEBHOOK or VERIFICATION_REQUEST_NOT_FOUND).
 */

import { z } from 'zod';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';
import { DisputeErrors } from '@/server/error_definitions/DisputeErrors';
import { logger } from '@/server/logging/logger';

// ---------------------------------------------------------------------------
// Zod Schemas
// ---------------------------------------------------------------------------

/**
 * Schema for the raw webhook body received from the SMS provider.
 */
export const SmsDisputeWebhookBodySchema = z.object({
  token: z.string().min(1),
  claimantId: z.string().min(1),
  disputedClaimIds: z.array(z.string().min(1)).min(1),
});

/**
 * Schema for the structured dispute payload returned after validation.
 */
export const SmsDisputePayloadSchema = z.object({
  claimantId: z.string().min(1),
  disputedClaimIds: z.array(z.string().min(1)).min(1),
});

export type SmsDisputePayload = z.infer<typeof SmsDisputePayloadSchema>;

// ---------------------------------------------------------------------------
// Endpoint Logic
// ---------------------------------------------------------------------------

/**
 * Parse and validate an SMS dispute webhook payload.
 *
 * 1. Validate the payload structure via Zod.
 * 2. Verify the token corresponds to an active verification request.
 * 3. Return structured dispute data.
 *
 * @param payload - Raw webhook body (unknown)
 * @returns Structured dispute payload { claimantId, disputedClaimIds }
 * @throws DisputeError MALFORMED_WEBHOOK if payload fails validation
 * @throws DisputeError VERIFICATION_REQUEST_NOT_FOUND if token has no active request
 */
export async function parseSmsDisputeWebhook(
  payload: unknown,
): Promise<SmsDisputePayload> {
  // Step 1: Validate webhook body structure
  const parseResult = SmsDisputeWebhookBodySchema.safeParse(payload);

  if (!parseResult.success) {
    logger.warn('Malformed SMS dispute webhook payload', {
      path: '322-handle-disputed-claims-and-block-drafting',
      resource: 'api-m5g7',
    });
    throw DisputeErrors.MALFORMED_WEBHOOK();
  }

  const { token, claimantId, disputedClaimIds } = parseResult.data;

  // Step 2: Verify token corresponds to active verification request
  const verificationRequest = await VerificationRequestDAO.findByToken(token);

  if (!verificationRequest) {
    logger.warn('No active verification request for dispute token', {
      path: '322-handle-disputed-claims-and-block-drafting',
      resource: 'api-m5g7',
    });
    throw DisputeErrors.VERIFICATION_REQUEST_NOT_FOUND();
  }

  // Step 3: Return structured dispute data
  return {
    claimantId,
    disputedClaimIds,
  };
}
