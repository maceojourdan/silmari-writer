/**
 * evaluateBehavioralQuestion - Typed API contract for the
 * behavioral question evaluate endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Includes retry logic (max 5 attempts) for network errors.
 * Client errors (4xx) are not retried.
 */

import { z } from 'zod';

/**
 * Request payload for evaluating a behavioral question.
 */
export interface EvaluateBehavioralQuestionRequest {
  sessionId: string;
  objective: string;
  actions: string[];
  obstacles: string[];
  outcome: string;
  roleClarity: string;
}

/**
 * Response schema for successful evaluation.
 */
export const EvaluateBehavioralQuestionResponseSchema = z.object({
  eligible: z.boolean(),
  questionId: z.string().min(1),
  status: z.enum(['DRAFT', 'VERIFY']),
  updatedAt: z.string(),
});

export type EvaluateBehavioralQuestionResponse = z.infer<
  typeof EvaluateBehavioralQuestionResponseSchema
>;

const MAX_RETRIES = 5;

/**
 * Typed function that sends the evaluation request with retry logic.
 *
 * - Retries up to 5 times on network errors (fetch rejection).
 * - Does NOT retry on 4xx client errors.
 * - Retries on 5xx server errors.
 */
export async function evaluateBehavioralQuestion(
  payload: EvaluateBehavioralQuestionRequest,
): Promise<EvaluateBehavioralQuestionResponse> {
  let lastError: Error | null = null;

  for (let attempt = 1; attempt <= MAX_RETRIES; attempt++) {
    try {
      const response = await fetch('/api/behavioral-question/evaluate', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload),
      });

      if (!response.ok) {
        const errorBody = await response.json().catch(() => ({}));
        const errorMessage =
          errorBody.message ||
          `Evaluate behavioral question failed with status ${response.status}`;

        // Don't retry client errors (4xx)
        if (response.status >= 400 && response.status < 500) {
          throw new Error(errorMessage);
        }

        // Retry server errors (5xx)
        lastError = new Error(errorMessage);
        continue;
      }

      const data = await response.json();
      const parsed = EvaluateBehavioralQuestionResponseSchema.safeParse(data);

      if (!parsed.success) {
        throw new Error(
          `Invalid response from evaluate endpoint: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
        );
      }

      return parsed.data;
    } catch (error) {
      if (error instanceof Error) {
        // If it's a client error (thrown above with no retry), re-throw immediately
        if (
          !error.message.includes('Network') &&
          !error.message.includes('fetch') &&
          !error.message.includes('failed with status 5')
        ) {
          throw error;
        }
        lastError = error;
      } else {
        lastError = new Error(String(error));
      }
    }
  }

  throw lastError || new Error('Evaluate behavioral question failed after retries');
}
