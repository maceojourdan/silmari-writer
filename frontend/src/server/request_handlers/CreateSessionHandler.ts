/**
 * CreateSessionHandler - Orchestrates voice-assisted session creation:
 * validates request → delegates to SessionInitializationService → returns result.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Known errors (SessionError) are rethrown as-is.
 * Unknown errors are logged and wrapped in HttpErrors.internal.
 */

import type { SessionInitializationResult } from '@/server/data_structures/AnswerSession';
import { SessionInitializationService } from '@/server/services/SessionInitializationService';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { HttpError, HttpErrors } from '@/server/error_definitions/HttpErrors';
import { logger } from '@/server/logging/logger';

export interface CreateSessionCommand {
  userId: string;
}

export const CreateSessionHandler = {
  /**
   * Handle the session creation request:
   * 1. Validate userId from auth context
   * 2. Delegate to SessionInitializationService
   * 3. Return result with sessionId and state
   *
   * @param command - Validated command with userId from auth context
   * @returns SessionInitializationResult
   * @throws HttpError with VALIDATION_ERROR if userId is missing
   * @throws SessionError for persistence failures
   * @throws HttpError with INTERNAL_ERROR for unexpected failures
   */
  async handle(command: CreateSessionCommand): Promise<SessionInitializationResult> {
    try {
      // Validate command
      if (!command.userId || command.userId.trim() === '') {
        throw HttpErrors.validation('Missing or empty userId in auth context');
      }

      // Delegate to service
      const result = await SessionInitializationService.initializeSession(command.userId);

      return result;
    } catch (error) {
      // Known session errors → rethrow
      if (error instanceof SessionError) {
        throw error;
      }

      // Known HTTP errors → rethrow
      if (error instanceof HttpError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during session creation',
        error,
        {
          path: '306-initiate-voice-assisted-answer-session',
          resource: 'api-n8k2',
        },
      );

      throw HttpErrors.internal(
        `Unexpected error during session creation: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
