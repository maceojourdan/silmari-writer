/**
 * FinalizeSessionService - Orchestrates the session finalization flow:
 * validate eligibility → update session state → persist StoryRecord.
 *
 * Resource: db-h2s4 (service)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 *
 * Uses sequential operations with manual rollback on StoryRecord failure.
 * If session state update succeeds but StoryRecord persistence fails,
 * the session state is rolled back to ACTIVE.
 */

import { SessionStoryRecordDAO, type SessionForFinalization } from '@/server/data_access_objects/SessionStoryRecordDAO';
import { FinalizeSessionErrors } from '@/server/error_definitions/FinalizeSessionErrors';
import { SessionState, type FinalizeSessionResult } from '@/server/data_structures/Session';
import type { StoryRecord } from '@/server/data_structures/StoryRecord';
import { logger } from '@/server/logging/logger';

export const FinalizeSessionService = {
  /**
   * Step 2: Validate session eligibility for finalization.
   *
   * Checks:
   * 1. Session exists
   * 2. Session state is ACTIVE
   * 3. Required inputs are complete
   *
   * @param sessionId - The session ID to validate
   * @returns The validated session entity
   * @throws FinalizeSessionError with SESSION_NOT_FOUND if session doesn't exist
   * @throws FinalizeSessionError with INVALID_SESSION_STATE if state !== ACTIVE
   * @throws FinalizeSessionError with INCOMPLETE_SESSION if requiredInputsComplete is false
   */
  async validateEligibility(sessionId: string): Promise<SessionForFinalization> {
    const session = await SessionStoryRecordDAO.findSessionById(sessionId);

    if (!session) {
      throw FinalizeSessionErrors.SessionNotFound(
        `Session with id ${sessionId} not found`,
      );
    }

    if (session.state !== SessionState.ACTIVE) {
      throw FinalizeSessionErrors.InvalidSessionState(
        `Session ${sessionId} is in state ${session.state}, expected ACTIVE`,
      );
    }

    if (!session.requiredInputsComplete) {
      throw FinalizeSessionErrors.IncompleteSession(
        `Session ${sessionId} has incomplete required inputs`,
      );
    }

    return session;
  },

  /**
   * Step 3: Update session state to FINALIZE.
   *
   * @param sessionId - The session ID to update
   * @returns The updated session
   * @throws FinalizeSessionError with SESSION_PERSISTENCE_ERROR on database failure
   */
  async updateState(sessionId: string): Promise<void> {
    try {
      await SessionStoryRecordDAO.updateSessionState(sessionId, SessionState.FINALIZE);
    } catch (error) {
      throw FinalizeSessionErrors.SessionPersistenceError(
        `Failed to update session state: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },

  /**
   * Step 4: Persist StoryRecord with FINALIZED status and responses.
   * On failure, rolls back session state to ACTIVE.
   *
   * @param sessionId - The session ID
   * @param responses - The collected voice responses
   * @returns The persisted StoryRecord
   * @throws FinalizeSessionError with STORY_RECORD_PERSISTENCE_ERROR on failure
   */
  async persistStoryRecord(sessionId: string, responses: string[]): Promise<StoryRecord> {
    try {
      const storyRecord = await SessionStoryRecordDAO.upsertStoryRecord(
        sessionId,
        responses,
        'FINALIZED',
      );
      return storyRecord;
    } catch (error) {
      // Rollback: restore session state to ACTIVE
      try {
        await SessionStoryRecordDAO.updateSessionState(sessionId, SessionState.ACTIVE);
      } catch (rollbackError) {
        // Log rollback failure but throw the original error
        logger.error(
          'Failed to rollback session state after StoryRecord persistence failure',
          rollbackError,
          { path: '308-finalize-voice-session-and-persist-storyrecord', resource: 'db-h2s4' },
        );
      }

      throw FinalizeSessionErrors.StoryRecordPersistenceError(
        `Failed to persist StoryRecord: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },

  /**
   * Full finalization flow: validate → update state → persist StoryRecord.
   *
   * @param sessionId - The session ID to finalize
   * @returns FinalizeSessionResult with sessionState and storyRecordStatus
   */
  async finalize(sessionId: string): Promise<FinalizeSessionResult> {
    // Step 2: Validate eligibility
    const session = await this.validateEligibility(sessionId);

    // Step 3: Update session state to FINALIZE
    await this.updateState(sessionId);

    // Step 4: Persist StoryRecord with FINALIZED status
    await this.persistStoryRecord(sessionId, session.responses);

    // Return confirmation
    return {
      sessionState: 'FINALIZE',
      storyRecordStatus: 'FINALIZED',
    };
  },
} as const;
