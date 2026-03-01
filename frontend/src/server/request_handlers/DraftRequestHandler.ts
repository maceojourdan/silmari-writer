/**
 * DraftRequestHandler - Delivers updated draft response to the caller.
 *
 * Orchestrates the full draft flow:
 * 1. DraftProcessChain.execute (trigger + load)
 * 2. DraftService.filterConfirmedClaims (filter)
 * 3. DraftService.generateDraft (generate)
 * 4. StoryRecordDAO.updateDraft (persist)
 * 5. Validate and return response
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { DraftProcessChain } from '@/server/process_chains/DraftProcessChain';
import { DraftService } from '@/server/services/DraftService';
import { StoryRecordDAO } from '@/server/data_access_objects/StoryRecordDAO';
import {
  DraftResponseSchema,
  type DraftResponse,
} from '@/server/data_structures/DraftStoryRecord';
import { DraftApiError, DraftError } from '@/server/error_definitions/DraftErrors';

export const DraftRequestHandler = {
  /**
   * Handle a draft request for a given StoryRecord.
   *
   * Runs the full process chain, transforms the result into a response,
   * and validates it against DraftResponseSchema.
   */
  async handle(storyRecordId: string): Promise<DraftResponse> {
    try {
      // Step 1: Trigger DRAFT execution (validates state)
      const context = await DraftProcessChain.execute(storyRecordId);

      // Step 3: Filter unconfirmed hard claims
      const filteredClaims = DraftService.filterConfirmedClaims(context.storyRecord);

      // Step 4: Generate draft text and claims_used
      const draftPayload = DraftService.generateDraft(filteredClaims);

      // Step 5: Persist draft and metadata
      const persisted = await StoryRecordDAO.updateDraft(storyRecordId, draftPayload);

      // Step 6: Transform to response and validate
      const response = {
        draft_text: persisted.draft_text,
        claims_used: persisted.claims_used,
      };

      const parsed = DraftResponseSchema.safeParse(response);

      if (!parsed.success) {
        throw DraftApiError.RESPONSE_TRANSFORM_FAILED(
          `Response validation failed: ${parsed.error.message}`,
        );
      }

      return parsed.data;
    } catch (error) {
      // Re-throw DraftErrors as-is
      if (error instanceof DraftError) {
        throw error;
      }

      // Wrap unexpected errors
      throw DraftApiError.RESPONSE_TRANSFORM_FAILED(
        `Unexpected error: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
