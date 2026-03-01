/**
 * finalizeSession - Typed API contract for the session finalization endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const FinalizeSessionRequestSchema = z.object({
  sessionId: z.string().min(1),
});

export type FinalizeSessionRequest = z.infer<typeof FinalizeSessionRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const FinalizeSessionResponseSchema = z.object({
  sessionState: z.literal('FINALIZE'),
  storyRecordStatus: z.literal('FINALIZED'),
});

export type FinalizeSessionResponse = z.infer<typeof FinalizeSessionResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the finalize session request.
 * Validates input via Zod schema before sending.
 * Validates response via Zod schema on receipt.
 * Logs errors via frontendLogger on failure.
 */
export async function finalizeSession(
  request: { sessionId: string },
): Promise<FinalizeSessionResponse> {
  try {
    // Validate request before sending
    const parseResult = FinalizeSessionRequestSchema.safeParse(request);
    if (!parseResult.success) {
      throw SharedErrors.RequestValidationError(
        `REQUEST_VALIDATION_ERROR: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    const { sessionId } = parseResult.data;

    const response = await fetch(`/api/sessions/${sessionId}/finalize`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(parseResult.data),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new Error(
        errorBody.message || `Finalize session request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = FinalizeSessionResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from finalize session: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Finalize session request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'finalizeSession', module: 'api_contracts' },
    );
    throw error;
  }
}
