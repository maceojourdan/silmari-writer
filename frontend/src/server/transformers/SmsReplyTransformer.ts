/**
 * SmsReplyTransformer - Parses and maps raw SMS reply payloads
 * into structured truth-check update requests.
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * Parses Twilio webhook payload and extracts verdict + phone number.
 * Correlates the reply to a claim via ClaimDAO.
 */

import { z } from 'zod';
import type { TruthCheckUpdateRequest, TruthCheckVerdict } from '@/server/data_structures/Claim';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { WebhookErrors } from '@/server/error_definitions/WebhookErrors';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Twilio webhook payload schema
// ---------------------------------------------------------------------------

export const TwilioSmsPayloadSchema = z.object({
  From: z.string().min(1),
  Body: z.string().min(1),
  MessageSid: z.string().min(1),
  To: z.string().optional(),
  AccountSid: z.string().optional(),
});

export type TwilioSmsPayload = z.infer<typeof TwilioSmsPayloadSchema>;

// ---------------------------------------------------------------------------
// Transformer
// ---------------------------------------------------------------------------

export const SmsReplyTransformer = {
  /**
   * Parse a raw webhook payload into a validated Twilio SMS payload.
   *
   * @throws WebhookErrors.INVALID_WEBHOOK_PAYLOAD if payload is malformed
   */
  parsePayload(payload: unknown): TwilioSmsPayload {
    const result = TwilioSmsPayloadSchema.safeParse(payload);

    if (!result.success) {
      throw WebhookErrors.INVALID_WEBHOOK_PAYLOAD(
        `Invalid SMS webhook payload: ${result.error.issues.map(i => i.message).join(', ')}`,
      );
    }

    return result.data;
  },

  /**
   * Extract verdict from the SMS body text.
   *
   * Recognizes: CONFIRM, DENY (case-insensitive)
   * Returns null if body doesn't match known verdicts.
   */
  extractVerdict(body: string): TruthCheckVerdict | null {
    const normalized = body.trim().toUpperCase();

    if (normalized === 'CONFIRM' || normalized === 'YES' || normalized === 'CONFIRMED') {
      return 'confirmed';
    }

    if (normalized === 'DENY' || normalized === 'NO' || normalized === 'DENIED') {
      return 'denied';
    }

    return null;
  },

  /**
   * Parse and correlate a webhook payload to a structured truth-check update.
   *
   * 1. Parse and validate the Twilio payload
   * 2. Extract verdict from body
   * 3. Correlate sender phone number to a claim
   * 4. Return structured TruthCheckUpdateRequest
   *
   * @throws WebhookErrors.INVALID_WEBHOOK_PAYLOAD if payload is malformed
   * @throws WebhookErrors.CLAIM_NOT_FOUND if no claim correlates
   */
  async parse(payload: unknown): Promise<TruthCheckUpdateRequest> {
    // 1. Validate payload
    const smsPayload = this.parsePayload(payload);

    // 2. Extract verdict
    const verdict = this.extractVerdict(smsPayload.Body);

    if (!verdict) {
      frontendLogger.warn('SMS reply body does not match known verdict', {
        path: '305-followup-sms-for-uncertain-claim',
        resource: 'cfg-h5v9',
        from: smsPayload.From,
        body: smsPayload.Body,
      });
      throw WebhookErrors.INVALID_WEBHOOK_PAYLOAD(
        `Unrecognized reply: "${smsPayload.Body}". Expected CONFIRM or DENY.`,
      );
    }

    // 3. Correlate to claim
    const claim = await ClaimDAO.findByPhoneNumber(smsPayload.From);

    if (!claim) {
      frontendLogger.error('Cannot correlate SMS reply to a claim', undefined, {
        path: '305-followup-sms-for-uncertain-claim',
        resource: 'cfg-h5v9',
        from: smsPayload.From,
      });
      throw WebhookErrors.CLAIM_NOT_FOUND(
        `No claim found for phone number ${smsPayload.From}`,
      );
    }

    // 4. Return structured update
    return {
      claimId: claim.id,
      verdict,
      source: `sms:${smsPayload.MessageSid}`,
    };
  },
} as const;
