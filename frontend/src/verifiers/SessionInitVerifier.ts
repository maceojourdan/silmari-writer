/**
 * SessionInitVerifier - Validates user inputs for session initialization
 * (resume, job link/text, question text) on the client side.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 294-parse-and-store-session-input-objects
 */

import { z } from 'zod';

/**
 * Zod schema for session initialization input.
 *
 * Requires:
 * - resume: non-empty string
 * - questionText: non-empty string
 * - At least one of jobText or jobLink
 * - jobLink (if provided) must be a valid URL
 */
export const SessionInitInputSchema = z
  .object({
    resume: z.string().min(1, 'Resume content is required'),
    jobText: z.string().min(1).optional(),
    jobLink: z.string().url('jobLink must be a valid URL').optional(),
    questionText: z.string().min(1, 'Question text is required'),
  })
  .refine(
    (data) =>
      (data.jobText !== undefined && data.jobText.length > 0) ||
      (data.jobLink !== undefined && data.jobLink.length > 0),
    {
      message: 'At least one of jobText or jobLink is required',
      path: ['job'],
    },
  );

export type SessionInitInput = z.infer<typeof SessionInitInputSchema>;

type ValidationSuccess = { success: true; data: SessionInitInput };
type ValidationFailure = { success: false; errors: string[] };
type ValidationResult = ValidationSuccess | ValidationFailure;

/**
 * Validates unknown input for session initialization.
 * Returns a discriminated union result.
 */
export function validateSessionInitInput(
  payload: unknown,
): ValidationResult {
  const result = SessionInitInputSchema.safeParse(payload);
  if (result.success) {
    return { success: true, data: result.data };
  }
  const errors = result.error.issues.map(
    (issue) => `${issue.path.join('.')}: ${issue.message}`,
  );
  return { success: false, errors };
}
