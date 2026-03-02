/**
 * finalizeAnswer - Typed API contract for the finalize answer endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 333-finalize-answer-locks-editing
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const FinalizeAnswerRequestSchema = z.object({
  answerId: z.string().min(1),
});

export type FinalizeAnswerRequest = z.infer<typeof FinalizeAnswerRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const FinalizeAnswerResponseSchema = z.object({
  id: z.string().min(1),
  finalized: z.literal(true),
  editable: z.literal(false),
});

export type FinalizeAnswerResponse = z.infer<typeof FinalizeAnswerResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the finalize answer request.
 * Validates response via Zod schema on receipt.
 */
export async function finalizeAnswer(
  payload: FinalizeAnswerRequest,
): Promise<FinalizeAnswerResponse> {
  const response = await fetch(`/api/answers/${payload.answerId}/finalize`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Finalize answer failed with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = FinalizeAnswerResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from finalize answer: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
