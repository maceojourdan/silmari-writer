/**
 * answerUpdateVerifier - Validates client-side edit submission before API call.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 337-prevent-edit-of-locked-answer
 *
 * Validates:
 *   - id is a non-empty string (after trimming)
 *   - content is a non-empty string (after trimming)
 *
 * Returns:
 *   - { valid: true, payload: UpdateAnswerPayload } on success
 *   - { valid: false, errors: string[] } on failure
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type UpdateAnswerPayload = {
  id: string;
  content: string;
};

type ValidationSuccess = { valid: true; payload: UpdateAnswerPayload };
type ValidationFailure = { valid: false; errors: string[] };
export type AnswerUpdateValidationResult = ValidationSuccess | ValidationFailure;

// ---------------------------------------------------------------------------
// Schema
// ---------------------------------------------------------------------------

const AnswerUpdateSchema = z.object({
  id: z.string().min(1, 'Answer ID is required'),
  content: z.string().min(1, 'Content is required'),
});

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

export function validateAnswerUpdate(
  id: string,
  content: string,
): AnswerUpdateValidationResult {
  const trimmedId = id.trim();
  const trimmedContent = content.trim();

  const parsed = AnswerUpdateSchema.safeParse({
    id: trimmedId,
    content: trimmedContent,
  });

  if (!parsed.success) {
    const errors = parsed.error.issues.map((issue) => issue.message);
    return { valid: false, errors };
  }

  return {
    valid: true,
    payload: { id: trimmedId, content: trimmedContent },
  };
}
