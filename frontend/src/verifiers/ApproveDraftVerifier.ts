/**
 * ApproveDraftVerifier - Validates required identifiers before sending
 * an approval request to the backend.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

import { z } from 'zod';

/**
 * Zod schema requiring all five identifiers as non-empty strings.
 */
export const ApproveDraftPayloadSchema = z.object({
  draftId: z.string().min(1, 'draftId is required'),
  resumeId: z.string().min(1, 'resumeId is required'),
  jobId: z.string().min(1, 'jobId is required'),
  questionId: z.string().min(1, 'questionId is required'),
  voiceSessionId: z.string().min(1, 'voiceSessionId is required'),
});

export type ApproveDraftPayload = z.infer<typeof ApproveDraftPayloadSchema>;

type ValidationSuccess = { success: true; data: ApproveDraftPayload };
type ValidationFailure = { success: false; errors: string[] };
type ValidationResult = ValidationSuccess | ValidationFailure;

/**
 * Validates an unknown payload and returns a typed result.
 */
export function validateApproveDraftPayload(
  payload: unknown,
): ValidationResult {
  const result = ApproveDraftPayloadSchema.safeParse(payload);
  if (result.success) {
    return { success: true, data: result.data };
  }
  const errors = result.error.issues.map(
    (issue) => `${issue.path.join('.')}: ${issue.message}`,
  );
  return { success: false, errors };
}
