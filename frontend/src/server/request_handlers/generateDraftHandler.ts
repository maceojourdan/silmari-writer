/**
 * generateDraftHandler - Bridges the generate-draft endpoint to
 * the DraftGenerationService.
 *
 * Delegates to DraftGenerationService.generate() and maps errors
 * to HTTP-appropriate responses.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { DraftGenerationService } from '@/server/services/DraftGenerationService';
import type { GenerateDraftResponse } from '@/server/data_structures/StoryStructures';
import { GenerateDraftResponseSchema } from '@/server/data_structures/StoryStructures';
import { DraftError, DraftApiError } from '@/server/error_definitions/DraftErrors';
import { SharedError } from '@/server/error_definitions/SharedErrors';

export const generateDraftHandler = {
  /**
   * Handle a draft generation request for the given claim set.
   *
   * Calls DraftGenerationService.generate() and validates the response
   * against GenerateDraftResponseSchema before returning.
   */
  async handle(claimSetId: string): Promise<GenerateDraftResponse> {
    try {
      const draft = await DraftGenerationService.generate(claimSetId);

      const response: GenerateDraftResponse = { draft };

      const parsed = GenerateDraftResponseSchema.safeParse(response);
      if (!parsed.success) {
        throw DraftApiError.RESPONSE_TRANSFORM_FAILED(
          `Response validation failed: ${parsed.error.message}`,
        );
      }

      return parsed.data;
    } catch (error) {
      // Re-throw DraftErrors as-is (they already have status codes)
      if (error instanceof DraftError) {
        throw error;
      }

      // Re-throw SharedErrors as-is (they carry their own status codes)
      if (error instanceof SharedError) {
        throw error;
      }

      // Wrap unexpected errors
      throw DraftApiError.RESPONSE_TRANSFORM_FAILED(
        `Unexpected error: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
