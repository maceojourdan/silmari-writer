/**
 * editByVoice - Typed API contract for the edit-by-voice endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 330-edit-content-by-voice-from-review-screen
 *
 * Validates request payload and response via Zod schemas.
 * Sends POST to /api/edit-by-voice with contentId and instructionText.
 * Returns typed EditByVoiceResponse with updatedContent.
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const EditByVoiceRequestSchema = z.object({
  contentId: z.string().min(1, 'contentId is required'),
  instructionText: z.string().min(1, 'instructionText is required'),
});

export type EditByVoiceRequest = z.infer<typeof EditByVoiceRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const EditByVoiceResponseSchema = z.object({
  updatedContent: ContentEntitySchema,
});

export type EditByVoiceResponse = z.infer<typeof EditByVoiceResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the edit-by-voice request.
 * Validates response via Zod schema.
 * Logs errors via frontendLogger on failure.
 */
export async function editByVoice(
  payload: EditByVoiceRequest,
): Promise<EditByVoiceResponse> {
  try {
    const response = await fetch('/api/edit-by-voice', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      const error = new Error(
        errorBody.message || `Edit by voice failed with status ${response.status}`,
      );
      (error as any).code = errorBody.code;
      throw error;
    }

    const data = await response.json();
    const parsed = EditByVoiceResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from edit-by-voice: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Edit by voice request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'editByVoice', module: 'api_contracts' },
    );
    throw error;
  }
}
