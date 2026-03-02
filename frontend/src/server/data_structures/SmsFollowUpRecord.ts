/**
 * SmsFollowUpRecord - Zod schema and TypeScript types for the
 * SMS follow-up dispatch record stored after sending.
 *
 * Resource: db-f8n5 (data_structure)
 * Paths:
 *   - 335-trigger-sms-follow-up-on-answer-finalization
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Zod Schema
// ---------------------------------------------------------------------------

export const SmsFollowUpRecordSchema = z.object({
  id: z.string().uuid(),
  answerId: z.string().uuid(),
  phoneNumber: z.string().min(1),
  message: z.string().min(1),
  status: z.enum(['sent', 'failed']),
  messageId: z.string().optional(),
  createdAt: z.string(),
});

export type SmsFollowUpRecord = z.infer<typeof SmsFollowUpRecordSchema>;
