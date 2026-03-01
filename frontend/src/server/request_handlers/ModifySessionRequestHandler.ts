/**
 * ModifySessionRequestHandler - Bridges endpoint request to backend service logic
 * for session modification.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 309-reject-modifications-to-finalized-session
 *
 * Known errors (SessionError) are rethrown as-is.
 * Unknown errors are logged and wrapped in GenericErrors.InternalError.
 */

import { SessionModificationService } from '@/server/services/SessionModificationService';
import type { ModificationAction, ModificationResult } from '@/server/services/SessionModificationService';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export const ModifySessionRequestHandler = {
  /**
   * Handle a session modification request.
   *
   * 1. Forward sessionId and action to SessionModificationService
   * 2. Return service result (success or error)
   *
   * Rethrows SessionError as-is.
   * Wraps unknown errors in GenericErrors.InternalError.
   */
  async handle(
    sessionId: string,
    action: ModificationAction,
  ): Promise<ModificationResult> {
    try {
      return await SessionModificationService.processModification(sessionId, action);
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof SessionError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during session modification',
        error,
        { path: '309-reject-modifications-to-finalized-session', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during session modification: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
