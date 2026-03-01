/**
 * SessionApprovalService - Orchestrates session approval and state transition.
 *
 * Resource: db-h2s4 (service)
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * Validates that the session exists and is in DRAFT state,
 * then returns a transition instruction to update to FINALIZE.
 * Throws errors from StateTransitionErrors on failure.
 */

import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { StateTransitionErrors } from '@/server/error_definitions/StateTransitionErrors';
import type { SessionTransitionResult } from '@/server/data_structures/Session';

export const SessionApprovalService = {
  /**
   * Approve a session for transition from DRAFT to FINALIZE.
   *
   * 1. Load session via DAO
   * 2. Validate state === DRAFT
   * 3. Return transition instruction { newState: 'FINALIZE' }
   *
   * Throws SessionNotFound if session doesn't exist.
   * Throws InvalidStateTransition if session is not in DRAFT state.
   */
  async approve(sessionId: string): Promise<SessionTransitionResult> {
    const session = await SessionDAO.findById(sessionId);

    if (!session) {
      throw StateTransitionErrors.SessionNotFound(sessionId);
    }

    if (session.state !== 'DRAFT') {
      throw StateTransitionErrors.InvalidStateTransition(session.state, 'FINALIZE');
    }

    return { newState: 'FINALIZE' };
  },
} as const;
