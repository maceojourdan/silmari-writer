/**
 * modifySession - Typed API contract for the session modification endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 309-reject-modifications-to-finalized-session
 *
 * Sends a typed request to POST /api/sessions/[sessionId]/modify.
 * Returns a discriminated union result: { ok: true } | { ok: false; error }
 * Does not throw — errors are returned as values for the UI to handle.
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const ModifySessionRequestSchema = z.object({
  sessionId: z.string().min(1),
  action: z.enum(['ADD_VOICE', 'FINALIZE']),
});

export type ModifySessionRequest = z.infer<typeof ModifySessionRequestSchema>;

// ---------------------------------------------------------------------------
// Error Response Schema
// ---------------------------------------------------------------------------

export const ModifySessionErrorResponseSchema = z.object({
  code: z.string(),
  message: z.string(),
});

export type ModifySessionErrorResponse = z.infer<typeof ModifySessionErrorResponseSchema>;

// ---------------------------------------------------------------------------
// Result Types
// ---------------------------------------------------------------------------

export type ModifySessionResult =
  | { ok: true; data: unknown }
  | { ok: false; error: { code: string; message: string; status: number } };

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the session modification request.
 *
 * Does not throw — returns a discriminated union for the UI.
 * Logs errors via frontendLogger.
 */
export async function modifySession(
  sessionId: string,
  action: 'ADD_VOICE' | 'FINALIZE',
): Promise<ModifySessionResult> {
  try {
    const response = await fetch(`/api/sessions/${sessionId}/modify`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ sessionId, action }),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({
        code: 'UNKNOWN_ERROR',
        message: `Request failed with status ${response.status}`,
      }));

      return {
        ok: false,
        error: {
          code: errorBody.code || 'UNKNOWN_ERROR',
          message: errorBody.message || `Request failed with status ${response.status}`,
          status: response.status,
        },
      };
    }

    const data = await response.json();
    return { ok: true, data };
  } catch (error) {
    frontendLogger.error(
      'Session modification request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'modifySession', module: 'api_contracts' },
    );

    return {
      ok: false,
      error: {
        code: 'NETWORK_ERROR',
        message: error instanceof Error ? error.message : 'Network error',
        status: 0,
      },
    };
  }
}
