/**
 * createSession - Typed API contract for the voice-assisted session creation endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Sends a POST request to create a new voice-assisted answer session
 * and validates the response against the CreateSessionResponse Zod schema.
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const CreateSessionRequestSchema = z.object({});

export type CreateSessionRequest = z.infer<typeof CreateSessionRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const CreateSessionResponseSchema = z.object({
  sessionId: z.string().min(1),
  state: z.literal('INIT'),
});

export type CreateSessionResponse = z.infer<typeof CreateSessionResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the session creation request.
 * Validates response via Zod schema.
 * Logs errors via frontendLogger on failure.
 */
export async function createSession(
  authToken: string,
): Promise<CreateSessionResponse> {
  try {
    const response = await fetch('/api/sessions', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${authToken}`,
      },
      body: JSON.stringify({}),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new Error(
        errorBody.message || `Session creation failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = CreateSessionResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from sessions: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Session creation request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'createSession', module: 'api_contracts' },
    );

    throw error;
  }
}
