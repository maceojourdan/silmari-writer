/**
 * FinalizeSessionRequestHandler - Orchestrates the session finalization flow:
 * validate → service.finalize → response.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 *
 * Known errors (FinalizeSessionError) are rethrown as-is.
 * Unknown errors are logged and wrapped in HttpErrors.internal.
 */

import type { FinalizeSessionResult } from '@/server/data_structures/Session';
import { FinalizeSessionService } from '@/server/services/FinalizeSessionService';
import { FinalizeSessionError } from '@/server/error_definitions/FinalizeSessionErrors';
import { HttpError, HttpErrors } from '@/server/error_definitions/HttpErrors';
import { logger } from '@/server/logging/logger';

export const FinalizeSessionRequestHandler = {
  /**
   * Handle the session finalization request:
   * 1. Validate sessionId from request
   * 2. Delegate to FinalizeSessionService.finalize
   * 3. Return result with sessionState and storyRecordStatus
   *
   * @param sessionId - The session ID to finalize
   * @returns FinalizeSessionResult
   * @throws HttpError with VALIDATION_ERROR if sessionId is missing
   * @throws FinalizeSessionError for domain/persistence failures
   * @throws HttpError with INTERNAL_ERROR for unexpected failures
   */
  async handle(sessionId: string): Promise<FinalizeSessionResult> {
    try {
      // Validate sessionId
      if (!sessionId || sessionId.trim() === '') {
        throw HttpErrors.validation('Missing or empty sessionId');
      }

      // Delegate to service
      const result = await FinalizeSessionService.finalize(sessionId);

      return result;
    } catch (error) {
      // Known finalize session errors → rethrow
      if (error instanceof FinalizeSessionError) {
        throw error;
      }

      // Known HTTP errors → rethrow
      if (error instanceof HttpError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during session finalization',
        error,
        {
          path: '308-finalize-voice-session-and-persist-storyrecord',
          resource: 'api-n8k2',
        },
      );

      throw HttpErrors.internal(
        `Unexpected error during session finalization: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
