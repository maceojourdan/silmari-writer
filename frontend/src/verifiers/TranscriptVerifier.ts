/**
 * TranscriptVerifier - Validates transcript data received from TRANSCRIPT_FINAL
 * events before rendering in the UI.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { z } from 'zod';

/**
 * Zod schema for TRANSCRIPT_FINAL event payload validation.
 */
export const TranscriptPayloadSchema = z.object({
  type: z.literal('TRANSCRIPT_FINAL'),
  text: z.string().min(1, 'text must be non-empty'),
  sessionId: z.string().uuid('sessionId must be a valid UUID'),
});

export type TranscriptPayload = z.infer<typeof TranscriptPayloadSchema>;

type ValidationSuccess = { success: true; data: TranscriptPayload };
type ValidationFailure = { success: false; errors: string[] };
type ValidationResult = ValidationSuccess | ValidationFailure;

/**
 * Validates an unknown payload and returns a typed result.
 */
export function validateTranscriptPayload(
  payload: unknown,
): ValidationResult {
  const result = TranscriptPayloadSchema.safeParse(payload);
  if (result.success) {
    return { success: true, data: result.data };
  }
  const errors = result.error.issues.map(
    (issue) => `${issue.path.join('.')}: ${issue.message}`,
  );
  return { success: false, errors };
}
