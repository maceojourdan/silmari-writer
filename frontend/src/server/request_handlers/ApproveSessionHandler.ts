/**
 * ApproveSessionHandler - Orchestrates session approval flow:
 * service → DAO → logger.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * Known errors (StateTransitionError, PersistenceError) are rethrown as-is.
 * Unknown errors are logged and wrapped in GenericErrors.InternalError.
 */

import type { Session } from '@/server/data_structures/Session';
import { SessionApprovalService } from '@/server/services/SessionApprovalService';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { approvalLogger } from '@/server/logging/approvalLogger';
import { StateTransitionError } from '@/server/error_definitions/StateTransitionErrors';
import { PersistenceError } from '@/server/error_definitions/PersistenceErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export const ApproveSessionHandler = {
  /**
   * Handle the full session approval flow:
   * 1. Validate session exists + DRAFT state (service)
   * 2. Persist state transition (DAO)
   * 3. Log approval event (logger)
   * 4. Return updated session
   */
  async handle(sessionId: string): Promise<Session> {
    try {
      // Step 1: Validate and get transition instruction
      const transition = await SessionApprovalService.approve(sessionId);

      // Step 2: Persist state transition
      const updatedSession = await SessionDAO.updateState(sessionId, transition.newState);

      // Step 3: Log approval event
      await approvalLogger.logApproval(sessionId);

      // Step 4: Return updated session
      return updatedSession;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof StateTransitionError) {
        throw error;
      }
      if (error instanceof PersistenceError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during session approval',
        error,
        { path: '299-approve-draft-and-transition-to-finalize', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during session approval: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
