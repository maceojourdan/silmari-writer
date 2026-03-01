/**
 * SessionInitializationService - Orchestrates creation of an AnswerSession
 * and companion StoryRecord, both in INIT state.
 *
 * Resource: db-h2s4 (service)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Uses sequential inserts with manual rollback on failure.
 * If session creation succeeds but story creation fails,
 * the session is deleted (rollback).
 */

import type { SessionInitializationResult } from '@/server/data_structures/AnswerSession';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { SessionErrors } from '@/server/error_definitions/SessionErrors';

export const SessionInitializationService = {
  /**
   * Initialize a new voice-assisted answer session:
   * 1. Create AnswerSession in INIT state
   * 2. Create StoryRecord in INIT status linked to session
   *
   * On story creation failure, rolls back the session.
   *
   * @param userId - The authenticated user's ID
   * @returns SessionInitializationResult with sessionId, storyRecordId, and state
   * @throws SessionError with SESSION_PERSISTENCE_ERROR if session creation fails
   * @throws SessionError with STORY_PERSISTENCE_ERROR if story creation fails
   */
  async initializeSession(userId: string): Promise<SessionInitializationResult> {
    // Step 1: Create AnswerSession
    let session;
    try {
      session = await SessionDAO.createSession(userId);
    } catch (error) {
      throw SessionErrors.SessionPersistenceError(
        `Failed to create answer session: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    // Step 2: Create StoryRecord linked to session
    let storyRecord;
    try {
      storyRecord = await SessionDAO.createStoryRecord(session.id);
    } catch (error) {
      // Rollback: delete the session we just created
      try {
        await SessionDAO.deleteSession(session.id);
      } catch {
        // Log rollback failure but throw the original error
      }

      throw SessionErrors.StoryPersistenceError(
        `Failed to create story record: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    return {
      sessionId: session.id,
      storyRecordId: storyRecord.id,
      state: 'INIT',
    };
  },
} as const;
