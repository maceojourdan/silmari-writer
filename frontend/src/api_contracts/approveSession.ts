/**
 * approveSession - Typed API contract for the session approval endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const ApproveSessionRequestSchema = z.object({
  sessionId: z.string().uuid('sessionId must be a valid UUID'),
  action: z.literal('APPROVE'),
});

export type ApproveSessionRequest = z.infer<typeof ApproveSessionRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const ApproveSessionResponseSchema = z.object({
  id: z.string().uuid(),
  state: z.enum(['DRAFT', 'FINALIZE']),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type ApproveSessionResponse = z.infer<typeof ApproveSessionResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the session approval request.
 * Validates response via Zod schema.
 * Logs errors via clientLogger on failure.
 */
export async function approveSession(
  sessionId: string,
): Promise<ApproveSessionResponse> {
  try {
    const response = await fetch(`/api/sessions/${sessionId}/approve`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ sessionId, action: 'APPROVE' }),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new Error(
        errorBody.message || `Session approval failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = ApproveSessionResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from session approval: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Session approval request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'approveSession', module: 'api_contracts' },
    );
    throw error;
  }
}
