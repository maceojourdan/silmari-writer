/**
 * draftRequestVerifier - Validates client-side input before sending
 * a draft generation request to the backend.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { z } from 'zod';

/**
 * Zod schema requiring claimSetId as a valid UUID.
 */
export const DraftRequestPayloadSchema = z.object({
  claimSetId: z.string().uuid('claimSetId must be a valid UUID'),
});

export type DraftRequestPayload = z.infer<typeof DraftRequestPayloadSchema>;

type ValidationSuccess = { success: true; data: DraftRequestPayload };
type ValidationFailure = { success: false; errors: string[] };
type ValidationResult = ValidationSuccess | ValidationFailure;

/**
 * Validates an unknown payload and returns a typed result.
 */
export function validateDraftRequestPayload(
  payload: unknown,
): ValidationResult {
  const result = DraftRequestPayloadSchema.safeParse(payload);
  if (result.success) {
    return { success: true, data: result.data };
  }
  const errors = result.error.issues.map(
    (issue) => `${issue.path.join('.')}: ${issue.message}`,
  );
  return { success: false, errors };
}
