/**
 * updateAnswer - Typed API contract for the update answer endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 337-prevent-edit-of-locked-answer
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Custom Error Class
// ---------------------------------------------------------------------------

export class UpdateAnswerApiError extends Error {
  code: string;

  constructor(code: string, message: string) {
    super(message);
    this.name = 'UpdateAnswerApiError';
    this.code = code;
  }
}

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const UpdateAnswerRequestSchema = z.object({
  id: z.string().min(1),
  content: z.string().min(1),
});

export type UpdateAnswerRequest = z.infer<typeof UpdateAnswerRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const UpdateAnswerResponseSchema = z.object({
  id: z.string().min(1),
  content: z.string(),
});

export type UpdateAnswerResponse = z.infer<typeof UpdateAnswerResponseSchema>;

// ---------------------------------------------------------------------------
// Error Response Schema
// ---------------------------------------------------------------------------

export const UpdateAnswerErrorResponseSchema = z.object({
  code: z.string(),
  message: z.string(),
});

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the update answer request.
 * Validates response via Zod schema on receipt.
 *
 * On error responses, throws UpdateAnswerApiError with a `code` property
 * so that components can check `error.code === 'LOCKED_ANSWER_MODIFICATION_FORBIDDEN'`.
 */
export async function updateAnswer(
  payload: UpdateAnswerRequest,
): Promise<UpdateAnswerResponse> {
  const response = await fetch(`/api/answers/${payload.id}`, {
    method: 'PUT',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ content: payload.content }),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    const code = errorBody.code || 'UNKNOWN_ERROR';
    const message =
      errorBody.message || `Update answer failed with status ${response.status}`;
    throw new UpdateAnswerApiError(code, message);
  }

  const data = await response.json();
  const parsed = UpdateAnswerResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from update answer: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
