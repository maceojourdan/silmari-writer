/**
 * generateDraft - Typed API contract for the draft generation endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';
import { GenerateDraftResponseSchema } from '@/server/data_structures/StoryStructures';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const GenerateDraftContractRequestSchema = z.object({
  claimSetId: z.string().uuid(),
});

export type GenerateDraftContractRequest = z.infer<typeof GenerateDraftContractRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema (re-exported from data structures)
// ---------------------------------------------------------------------------

export { GenerateDraftResponseSchema };
export type { GenerateDraftResponse } from '@/server/data_structures/StoryStructures';

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the generate-draft request.
 * Validates input via Zod schema before sending.
 * Validates response via Zod schema on receipt.
 * Logs errors via frontendLogger on failure.
 */
export async function generateDraft(
  request: { claimSetId: string },
): Promise<z.infer<typeof GenerateDraftResponseSchema>> {
  try {
    // Validate request before sending
    const parseResult = GenerateDraftContractRequestSchema.safeParse(request);
    if (!parseResult.success) {
      throw SharedErrors.MalformedRequest(
        `MALFORMED_REQUEST: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    const response = await fetch('/api/generate-draft', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(parseResult.data),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new Error(
        errorBody.message || `Generate draft request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = GenerateDraftResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from generate-draft: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Generate draft request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'generateDraft', module: 'api_contracts' },
    );
    throw error;
  }
}
