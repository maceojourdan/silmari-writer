/**
 * User - Zod schema and TypeScript types for the User entity
 * with SMS opt-in and phone number fields.
 *
 * Resource: db-f8n5 (data_structure)
 * Paths:
 *   - 335-trigger-sms-follow-up-on-answer-finalization
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Zod Schema
// ---------------------------------------------------------------------------

export const UserSchema = z.object({
  id: z.string().uuid(),
  smsOptIn: z.boolean(),
  phoneNumber: z.string().optional(),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type User = z.infer<typeof UserSchema>;
