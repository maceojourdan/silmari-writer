/**
 * InitSessionRequestHandler - Orchestrates session initialization by
 * composing processor + service, and handling unexpected errors.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 294-parse-and-store-session-input-objects
 */

import type { SessionInitResult } from '@/server/data_structures/SessionObjects';
import type { RawSessionInput } from '@/server/transformers/SessionInputTransformer';
import { SessionInputProcessor } from '@/server/processors/SessionInputProcessor';
import { SessionInitService } from '@/server/services/SessionInitService';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export const InitSessionRequestHandler = {
  /**
   * Handle the full session initialization flow:
   * 1. Process raw input (transform + validate)
   * 2. Initialize session (persist)
   * 3. Return result with IDs
   *
   * Known errors (SessionError) are rethrown as-is.
   * Unknown errors are logged and wrapped in GenericErrors.InternalError.
   */
  async handle(payload: RawSessionInput): Promise<SessionInitResult> {
    try {
      // Step 1: Process raw input into structured objects
      const parsedInput = await SessionInputProcessor.process(payload);

      // Step 2: Persist and create session
      const result = await SessionInitService.initialize(parsedInput);

      return result;
    } catch (error) {
      // Known session errors → rethrow
      if (error instanceof SessionError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during session initialization',
        error,
        { path: '294-parse-and-store-session-input-objects', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during session initialization: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
