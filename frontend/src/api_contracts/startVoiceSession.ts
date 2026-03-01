/**
 * startVoiceSession - Typed API contract for the voice session start endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * Sends a POST request with consent flag and validates the response.
 * Implements exponential retry (max 2 retries) on network failure.
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const StartVoiceSessionRequestSchema = z.object({
  consent: z.literal(true),
});

export type StartVoiceSessionRequest = z.infer<typeof StartVoiceSessionRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const StartVoiceSessionResponseSchema = z.object({
  sessionStatus: z.enum(['INIT']),
});

export type StartVoiceSessionResponse = z.infer<typeof StartVoiceSessionResponseSchema>;

// ---------------------------------------------------------------------------
// Retry Configuration
// ---------------------------------------------------------------------------

const MAX_RETRIES = 2;
const BASE_DELAY_MS = 100;

async function delay(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the voice session start request.
 * Validates response via Zod schema.
 * Retries on network failure with exponential backoff (max 2 retries).
 * Logs errors via frontendLogger on final failure.
 */
export async function startVoiceSession(
  payload: StartVoiceSessionRequest,
): Promise<StartVoiceSessionResponse> {
  let lastError: Error | undefined;

  for (let attempt = 0; attempt <= MAX_RETRIES; attempt++) {
    try {
      if (attempt > 0) {
        await delay(BASE_DELAY_MS * Math.pow(2, attempt - 1));
      }

      const response = await fetch('/api/voice-session/start', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload),
      });

      if (!response.ok) {
        const errorBody = await response.json().catch(() => ({}));
        throw new Error(
          errorBody.message || `Voice session start failed with status ${response.status}`,
        );
      }

      const data = await response.json();
      const parsed = StartVoiceSessionResponseSchema.safeParse(data);

      if (!parsed.success) {
        throw new Error(
          `Invalid response from voice-session/start: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
        );
      }

      return parsed.data;
    } catch (error) {
      lastError = error instanceof Error ? error : new Error(String(error));

      // Only retry on network errors (TypeError: Failed to fetch), not server errors
      if (error instanceof TypeError && attempt < MAX_RETRIES) {
        continue;
      }

      // Non-retryable error or final retry exhausted
      break;
    }
  }

  // All retries exhausted or non-retryable error
  frontendLogger.error(
    'Voice session start request failed after retries',
    lastError,
    { action: 'startVoiceSession', module: 'api_contracts' },
  );

  throw lastError;
}
