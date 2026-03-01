/**
 * draftPreconditionsVerifier - Validates frontend preconditions
 * before sending a draft generation request.
 *
 * Returns { valid: boolean; message?: string } to match the
 * plan specification for path 327.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 */

import { z } from 'zod';

/**
 * Zod schema requiring storyRecordId as a non-empty string.
 */
export const DraftPreconditionsPayloadSchema = z.object({
  storyRecordId: z.string().min(1, 'storyRecordId is required'),
});

export type DraftPreconditionsPayload = z.infer<typeof DraftPreconditionsPayloadSchema>;

type ValidationSuccess = { valid: true };
type ValidationFailure = { valid: false; message: string };
type ValidationResult = ValidationSuccess | ValidationFailure;

/**
 * Validates an unknown payload and returns { valid, message? }.
 */
export function validateDraftPreconditions(
  payload: unknown,
): ValidationResult {
  const result = DraftPreconditionsPayloadSchema.safeParse(payload);
  if (result.success) {
    return { valid: true };
  }
  const message = result.error.issues
    .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
    .join('; ');
  return { valid: false, message };
}
