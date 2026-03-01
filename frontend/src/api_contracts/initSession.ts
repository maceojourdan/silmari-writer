/**
 * initSession - Typed API contract for the session initialization endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 294-parse-and-store-session-input-objects
 */

import { z } from 'zod';

/**
 * Request payload for session initialization.
 */
export interface InitSessionRequest {
  resume: string;
  jobText?: string;
  jobLink?: string;
  questionText: string;
}

/**
 * Response schema for successful session initialization.
 */
export const InitSessionResponseSchema = z.object({
  sessionId: z.string().min(1),
  resumeId: z.string().min(1),
  jobId: z.string().min(1),
  questionId: z.string().min(1),
});

export type InitSessionResponse = z.infer<typeof InitSessionResponseSchema>;

/**
 * Typed function that sends the session initialization request.
 */
export async function initSession(
  payload: InitSessionRequest,
): Promise<InitSessionResponse> {
  const response = await fetch('/api/session/init', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Session initialization failed with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = InitSessionResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from session/init: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
