/**
 * confirmTruthCheck - Typed API contract for the
 * truth check confirm endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Includes retry logic (max 3 attempts) for network errors.
 * Client errors (4xx) are not retried.
 */

import { z } from 'zod';

/**
 * Request payload for confirming a truth check.
 */
export interface ConfirmTruthCheckRequest {
  claim_id: string;
  status: 'confirmed' | 'denied';
  source: string;
}

/**
 * Response schema for successful confirmation.
 */
export const ConfirmTruthCheckResponseSchema = z.object({
  id: z.string().min(1),
  claim_id: z.string().min(1),
  status: z.enum(['confirmed', 'denied']),
  source: z.string().min(1),
  created_at: z.string(),
});

export type ConfirmTruthCheckResponse = z.infer<
  typeof ConfirmTruthCheckResponseSchema
>;

const MAX_RETRIES = 3;

/**
 * Typed function that sends the confirmation request with retry logic.
 *
 * - Retries up to 3 times total on network errors (fetch rejection).
 * - Does NOT retry on 4xx client errors.
 * - Retries on 5xx server errors.
 */
export async function confirmTruthCheck(
  payload: ConfirmTruthCheckRequest,
): Promise<ConfirmTruthCheckResponse> {
  let lastError: Error | null = null;

  for (let attempt = 1; attempt <= MAX_RETRIES; attempt++) {
    try {
      const response = await fetch('/api/truth-checks/confirm', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload),
      });

      if (!response.ok) {
        const errorBody = await response.json().catch(() => ({}));
        const errorMessage =
          errorBody.message ||
          `Confirm truth check failed with status ${response.status}`;

        // Don't retry client errors (4xx)
        if (response.status >= 400 && response.status < 500) {
          throw new Error(errorMessage);
        }

        // Retry server errors (5xx)
        lastError = new Error(errorMessage);
        continue;
      }

      const data = await response.json();
      const parsed = ConfirmTruthCheckResponseSchema.safeParse(data);

      if (!parsed.success) {
        throw new Error(
          `Invalid response from confirm endpoint: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
        );
      }

      return parsed.data;
    } catch (error) {
      if (error instanceof Error) {
        // If it's a client error (thrown above with no retry), re-throw immediately
        if (
          !error.message.includes('Failed to fetch') &&
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

  throw lastError || new Error('Confirm truth check failed after retries');
}
