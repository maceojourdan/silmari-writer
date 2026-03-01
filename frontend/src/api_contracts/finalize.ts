/**
 * finalize - Typed API contract for the draft finalization endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';
import { ExportArtifactSchema } from '@/server/data_structures/Draft';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const FinalizeRequestSchema = z.object({
  draftId: z.string().min(1),
  userId: z.string().min(1),
});

export type FinalizeRequest = z.infer<typeof FinalizeRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const FinalizeResponseSchema = z.object({
  artifact: ExportArtifactSchema,
  finalized: z.boolean(),
  metricsLogged: z.boolean(),
});

export type FinalizeResponse = z.infer<typeof FinalizeResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the finalize request.
 * Validates input via Zod schema before sending.
 * Validates response via Zod schema on receipt.
 * Logs errors via frontendLogger on failure.
 */
export async function finalizeDraft(
  request: { draftId: string; userId: string },
): Promise<FinalizeResponse> {
  try {
    // Validate request before sending
    const parseResult = FinalizeRequestSchema.safeParse(request);
    if (!parseResult.success) {
      throw SharedErrors.MalformedRequest(
        `MALFORMED_REQUEST: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    const response = await fetch('/api/finalize', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(parseResult.data),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new Error(
        errorBody.message || `Finalize request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = FinalizeResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from finalize: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Finalize request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'finalizeDraft', module: 'api_contracts' },
    );
    throw error;
  }
}
