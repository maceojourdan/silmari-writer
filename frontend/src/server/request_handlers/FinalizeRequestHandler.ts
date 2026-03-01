/**
 * FinalizeRequestHandler - Orchestrates the finalization flow:
 * processor.finalizeDraft → computeAndLogMetrics → response.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 300-finalize-approved-draft-and-log-metrics
 *
 * Known errors (FinalizeError) are rethrown as-is.
 * Unknown errors are logged and wrapped in GenericErrors.InternalError.
 */

import type { FinalizeResponse } from '@/api_contracts/finalize';
import { FinalizeProcessor } from '@/server/processors/FinalizeProcessor';
import { DraftDAO } from '@/server/data_access_objects/DraftDAO';
import { FinalizeError } from '@/server/error_definitions/FinalizeErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export const FinalizeRequestHandler = {
  /**
   * Handle the full finalization flow:
   * 1. Finalize draft (validate + transform + persist)
   * 2. Re-fetch finalized draft for metrics computation
   * 3. Compute and log metrics (non-fatal on failure)
   * 4. Return response
   */
  async handle(draftId: string, userId: string): Promise<FinalizeResponse> {
    try {
      // Step 1-3: Finalize the draft
      const { artifact } = await FinalizeProcessor.finalizeDraft(draftId);

      // Step 4: Compute and log metrics (non-fatal)
      const finalizedDraft = await DraftDAO.getDraftById(draftId);
      let metricsLogged = false;

      if (finalizedDraft) {
        metricsLogged = await FinalizeProcessor.computeAndLogMetrics(finalizedDraft);
      }

      // Step 5: Return response
      return {
        artifact,
        finalized: true,
        metricsLogged,
      };
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof FinalizeError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during finalization',
        error,
        { path: '300-finalize-approved-draft-and-log-metrics', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during finalization: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
