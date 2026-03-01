/**
 * Session - Zod schema and TypeScript types for the Session entity
 * with state field supporting draft-to-finalize transitions.
 *
 * Resource: db-f8n5 (data_structure)
 * Paths:
 *   - 299-approve-draft-and-transition-to-finalize
 *   - 308-finalize-voice-session-and-persist-storyrecord
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Session State Enum
// ---------------------------------------------------------------------------

export const SessionState = {
  DRAFT: 'DRAFT',
  DRAFT_ENABLED: 'DRAFT_ENABLED',
  ACTIVE: 'ACTIVE',
  FINALIZE: 'FINALIZE',
} as const;

export type SessionState = (typeof SessionState)[keyof typeof SessionState];

// ---------------------------------------------------------------------------
// Zod Schema
// ---------------------------------------------------------------------------

export const SessionSchema = z.object({
  id: z.string().uuid(),
  state: z.enum(['DRAFT', 'DRAFT_ENABLED', 'ACTIVE', 'FINALIZE']),
  requiredInputsComplete: z.boolean().optional(),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type Session = z.infer<typeof SessionSchema>;

// ---------------------------------------------------------------------------
// Transition Result
// ---------------------------------------------------------------------------

export const SessionTransitionResultSchema = z.object({
  newState: z.enum(['DRAFT', 'DRAFT_ENABLED', 'ACTIVE', 'FINALIZE']),
});

export type SessionTransitionResult = z.infer<typeof SessionTransitionResultSchema>;

// ---------------------------------------------------------------------------
// Finalize Session Response (Path 308)
// ---------------------------------------------------------------------------

export const FinalizeSessionResultSchema = z.object({
  sessionState: z.literal('FINALIZE'),
  storyRecordStatus: z.literal('FINALIZED'),
});

export type FinalizeSessionResult = z.infer<typeof FinalizeSessionResultSchema>;
