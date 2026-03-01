/**
 * StartVoiceSessionHandler - Orchestrates voice session start flow:
 * service validates consent → return result.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * Known errors (ConsentError) are rethrown as-is.
 * Unknown errors are logged and wrapped in GenericErrors.InternalError.
 */

import { VoiceSessionService, type ConsentValidationResult } from '@/server/services/VoiceSessionService';
import { ConsentError } from '@/server/error_definitions/ConsentErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export const StartVoiceSessionHandler = {
  /**
   * Handle the voice session start request:
   * 1. Validate consent via VoiceSessionService
   * 2. Return session status result
   *
   * @param payload - Object with consent flag
   * @returns ConsentValidationResult { authorized: true, sessionStatus: 'INIT' }
   * @throws ConsentError if consent is missing/false
   * @throws GenericError for unexpected failures
   */
  async handle(payload: { consent: boolean }): Promise<ConsentValidationResult> {
    try {
      const result = VoiceSessionService.validateConsent(payload);
      return result;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof ConsentError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during voice session start',
        error,
        {
          path: '302-enforce-affirmative-consent-before-voice-session',
          resource: 'api-n8k2',
        },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during voice session start: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
