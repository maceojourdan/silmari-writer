/**
 * FinalizeEvent - Zod schemas for the finalize completion event
 * and the SMS follow-up detection result.
 *
 * Resource: db-f8n5 (data_structure)
 * Paths:
 *   - 335-trigger-sms-follow-up-on-answer-finalization
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// FinalizeEvent — input to detectFinalizeCompletion
// ---------------------------------------------------------------------------

export const FinalizeEventSchema = z.object({
  answerId: z.string().uuid(),
  userId: z.string().uuid(),
  smsOptIn: z.boolean(),
  phoneNumber: z.string().optional(),
});

export type FinalizeEvent = z.infer<typeof FinalizeEventSchema>;

// ---------------------------------------------------------------------------
// DetectFinalizeResult — output from detectFinalizeCompletion
// ---------------------------------------------------------------------------

export const DetectFinalizeResultSchema = z.discriminatedUnion('shouldSend', [
  z.object({
    shouldSend: z.literal(true),
    answerId: z.string().uuid(),
    phoneNumber: z.string().min(1),
  }),
  z.object({
    shouldSend: z.literal(false),
  }),
]);

export type DetectFinalizeResult = z.infer<typeof DetectFinalizeResultSchema>;

// ---------------------------------------------------------------------------
// SmsPayload — structured payload from loadAnswerAndContact
// ---------------------------------------------------------------------------

export const SmsPayloadSchema = z.object({
  answerSummary: z.string().min(1),
  phoneNumber: z.string().min(1),
});

export type SmsPayload = z.infer<typeof SmsPayloadSchema>;

// ---------------------------------------------------------------------------
// SmsDeliveryResponse — response from sendSms
// ---------------------------------------------------------------------------

export const SmsDeliveryResponseSchema = z.object({
  status: z.enum(['sent', 'failed']),
  messageId: z.string().optional(),
});

export type SmsDeliveryResponse = z.infer<typeof SmsDeliveryResponseSchema>;
