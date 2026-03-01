/**
 * SessionModificationVerifier - Validates frontend modification payloads
 * before submission to the backend API.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 309-reject-modifications-to-finalized-session
 *
 * Uses Zod schema to enforce:
 * - sessionId must be a non-empty string
 * - action must be 'ADD_VOICE' or 'FINALIZE'
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Schema
// ---------------------------------------------------------------------------

export const ModifySessionPayloadSchema = z.object({
  sessionId: z.string().min(1, 'sessionId is required'),
  action: z.enum(['ADD_VOICE', 'FINALIZE']),
});

export type ModifySessionPayload = z.infer<typeof ModifySessionPayloadSchema>;

// ---------------------------------------------------------------------------
// Validator
// ---------------------------------------------------------------------------

type ValidationSuccess = { success: true; data: ModifySessionPayload };
type ValidationFailure = { success: false; errors: string[] };

/**
 * Validate a session modification payload.
 *
 * Returns { success: true; data: ModifySessionPayload } on valid input.
 * Returns { success: false; errors: string[] } on invalid input.
 */
export function validateModifySessionPayload(
  payload: unknown,
): ValidationSuccess | ValidationFailure {
  const result = ModifySessionPayloadSchema.safeParse(payload);

  if (result.success) {
    return { success: true, data: result.data };
  }

  const errors = result.error.issues.map(
    (issue) => `${issue.path.join('.')}: ${issue.message}`,
  );

  return { success: false, errors };
}
