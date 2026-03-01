/**
 * VoiceEvent - Zod schemas and TypeScript types for SAY and TRANSCRIPT_FINAL
 * events in the voice processing pipeline.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// SAY Event (input to pipeline)
// ---------------------------------------------------------------------------

export const SayEventSchema = z.object({
  type: z.literal('SAY'),
  sessionId: z.string().uuid('sessionId must be a valid UUID'),
  text: z.string().min(1, 'text must be non-empty'),
});

export type SayEvent = z.infer<typeof SayEventSchema>;

// ---------------------------------------------------------------------------
// SAY Event with Session Context (after step 1)
// ---------------------------------------------------------------------------

export const SayEventWithSessionContextSchema = SayEventSchema.extend({
  sessionContext: z.object({
    sessionId: z.string().uuid(),
    isActive: z.boolean(),
  }),
});

export type SayEventWithSessionContext = z.infer<typeof SayEventWithSessionContextSchema>;

// ---------------------------------------------------------------------------
// Validated SAY Command (after step 2)
// ---------------------------------------------------------------------------

export const ValidatedSayCommandSchema = z.object({
  sessionId: z.string().uuid(),
  text: z.string().min(1),
  validatedAt: z.string(),
});

export type ValidatedSayCommand = z.infer<typeof ValidatedSayCommandSchema>;

// ---------------------------------------------------------------------------
// Speech Synthesis Request (after step 3)
// ---------------------------------------------------------------------------

export const SpeechSynthesisRequestSchema = z.object({
  text: z.string().min(1),
  voiceId: z.string().min(1),
  sessionId: z.string().uuid(),
});

export type SpeechSynthesisRequest = z.infer<typeof SpeechSynthesisRequestSchema>;

// ---------------------------------------------------------------------------
// TRANSCRIPT_FINAL Event (step 5 output)
// ---------------------------------------------------------------------------

export const TranscriptFinalEventSchema = z.object({
  type: z.literal('TRANSCRIPT_FINAL'),
  text: z.string().min(1),
  sessionId: z.string().uuid(),
});

export type TranscriptFinalEvent = z.infer<typeof TranscriptFinalEventSchema>;
