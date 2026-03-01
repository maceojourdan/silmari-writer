/**
 * generateDraftHandler - Bridges the generate-draft endpoint to
 * the DraftGenerationService.
 *
 * Delegates to DraftGenerationService.generate() and maps errors
 * to HTTP-appropriate responses.
 *
 * Resource: api-n8k2 (request_handler)
 * Paths:
 *   - 325-generate-draft-from-confirmed-claims
 *   - 326-generate-draft-with-only-confirmed-claims
 *   - 327-prevent-draft-generation-without-confirmed-claims
 *   - 328-exclude-incomplete-claim-during-draft-generation
 */

import { DraftGenerationService } from '@/server/services/DraftGenerationService';
import type { GenerateDraftResponse } from '@/server/data_structures/StoryStructures';
import { GenerateDraftResponseSchema } from '@/server/data_structures/StoryStructures';
import type { CaseDraft, GenerateStoryDraftResponse, ExcludeIncompleteDraftResponse } from '@/server/data_structures/Claim';
import {
  GenerateCaseDraftResponseSchema,
  GenerateStoryDraftResponseSchema,
  ExcludeIncompleteDraftResponseSchema,
} from '@/server/data_structures/Claim';
import { DraftError, DraftApiError, DraftErrors326, DraftErrors327, DraftErrors328 } from '@/server/error_definitions/DraftErrors';
import { SharedError } from '@/server/error_definitions/SharedErrors';
import { logger } from '@/server/logging/logger';

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

  // -------------------------------------------------------------------------
  // Path 326: generate-draft-with-only-confirmed-claims
  // -------------------------------------------------------------------------

  /**
   * Handle a case-based draft generation request.
   *
   * Calls DraftGenerationService.generateCaseDraft() and validates
   * the response against GenerateCaseDraftResponseSchema.
   *
   * @throws DraftError on service failure (re-thrown)
   * @throws DraftErrors326.GenerationError on unexpected errors
   */
  async handleCaseDraft(caseId: string): Promise<CaseDraft> {
    try {
      const draft = await DraftGenerationService.generateCaseDraft(caseId);

      const parsed = GenerateCaseDraftResponseSchema.safeParse(draft);
      if (!parsed.success) {
        throw DraftErrors326.GenerationError(
          `Response validation failed: ${parsed.error.message}`,
        );
      }

      return parsed.data;
    } catch (error) {
      // Re-throw DraftErrors as-is
      if (error instanceof DraftError) {
        throw error;
      }

      // Log and wrap unexpected errors
      logger.error(
        'Case draft generation failed',
        error,
        { path: '326', resource: 'api-n8k2', caseId },
      );
      throw DraftErrors326.GenerationError(
        `Unexpected error: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },

  // -------------------------------------------------------------------------
  // Path 327: prevent-draft-generation-without-confirmed-claims
  // -------------------------------------------------------------------------

  /**
   * Handle a story-record-based draft generation request.
   *
   * Calls DraftGenerationService.checkConfirmedClaimsForStoryRecord()
   * to validate confirmed claims exist, then composes a response.
   *
   * @throws DraftError on service failure (re-thrown: NoConfirmedClaimsError, DataAccessError)
   * @throws DraftErrors327.GenericDraftError on unexpected errors
   */
  async handleStoryDraft(storyRecordId: string): Promise<GenerateStoryDraftResponse> {
    try {
      const confirmedClaims = await DraftGenerationService.checkConfirmedClaimsForStoryRecord(storyRecordId);

      const response: GenerateStoryDraftResponse = {
        storyRecordId,
        content: confirmedClaims.map((c) => c.content).join('\n\n'),
        claimsUsed: confirmedClaims.map((c) => c.id),
      };

      const parsed = GenerateStoryDraftResponseSchema.safeParse(response);
      if (!parsed.success) {
        throw DraftErrors327.GenericDraftError(
          `Response validation failed: ${parsed.error.message}`,
        );
      }

      return parsed.data;
    } catch (error) {
      // Re-throw DraftErrors as-is (they carry status codes)
      if (error instanceof DraftError) {
        throw error;
      }

      // Log and wrap unexpected errors
      logger.error(
        'Story draft generation failed',
        error,
        { path: '327', resource: 'api-n8k2', storyRecordId },
      );
      throw DraftErrors327.GenericDraftError(
        `Unexpected error: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },

  // -------------------------------------------------------------------------
  // Path 328: exclude-incomplete-claim-during-draft-generation
  // -------------------------------------------------------------------------

  /**
   * Handle a draft generation request that excludes incomplete claims.
   *
   * Normalizes the request into a DraftGenerationCommand, then calls
   * DraftGenerationService.generateDraftExcludingIncomplete() to orchestrate:
   *   1. Retrieve confirmed claims
   *   2. Partition by structural metadata completeness
   *   3. Assemble draft from complete claims only
   *   4. Build omission report for incomplete claims
   *
   * @throws DraftErrors328.InvalidDraftRequest on invalid input
   * @throws DraftErrors328.DataAccessError on DAO failure
   * @throws DraftErrors328.DraftAssemblyError on assembly failure
   * @throws DraftErrors328.ServerError on unexpected errors
   */
  async handleExcludeIncompleteDraft(sessionId: string): Promise<ExcludeIncompleteDraftResponse> {
    try {
      const result = await DraftGenerationService.generateDraftExcludingIncomplete(sessionId);

      const response: ExcludeIncompleteDraftResponse = {
        draft: result.draftContent,
        omissions: result.omissionReport,
      };

      const parsed = ExcludeIncompleteDraftResponseSchema.safeParse(response);
      if (!parsed.success) {
        throw DraftErrors328.ServerError(
          `Response validation failed: ${parsed.error.message}`,
        );
      }

      return parsed.data;
    } catch (error) {
      // Re-throw DraftErrors as-is (they carry status codes)
      if (error instanceof DraftError) {
        throw error;
      }

      // Log and wrap unexpected errors
      logger.error(
        'Exclude-incomplete draft generation failed',
        error,
        { path: '328', resource: 'api-n8k2', sessionId },
      );
      throw DraftErrors328.ServerError(
        `Unexpected error: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
