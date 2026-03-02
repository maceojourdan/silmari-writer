/**
 * SessionInitializationService - Orchestrates creation of an AnswerSession
 * plus bootstrap ORIENT context and companion StoryRecord, all in INIT state.
 *
 * Resource: db-h2s4 (service)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Uses sequential inserts with manual rollback on failure.
 * If downstream creation fails, service performs best-effort rollback
 * for created session/context records.
 */

import type { SessionInitializationResult } from '@/server/data_structures/AnswerSession';
import { SessionDAO, type BootstrapQuestionContext } from '@/server/data_access_objects/SessionDAO';
import { SessionErrors } from '@/server/error_definitions/SessionErrors';

export const SessionInitializationService = {
  /**
   * Initialize a new voice-assisted answer session:
   * 1. Create AnswerSession in INIT state
   * 2. Create bootstrap ORIENT context (question + requirements + stories)
   * 3. Create StoryRecord in INIT status linked to session + question
   *
   * On downstream failures, rolls back created records best-effort.
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

    // Step 2: Create bootstrap ORIENT context (question + requirements + stories)
    let questionContext: BootstrapQuestionContext;
    try {
      questionContext = await SessionDAO.createBootstrapQuestionContext();
    } catch (error) {
      try {
        await SessionDAO.deleteSession(session.id);
      } catch {
        // Best-effort rollback.
      }

      throw SessionErrors.SessionPersistenceError(
        `Failed to create bootstrap question context: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    // Step 3: Create StoryRecord linked to session and bootstrap question
    let storyRecord;
    try {
      storyRecord = await SessionDAO.createStoryRecord(session.id, userId, questionContext.questionId);
    } catch (error) {
      // Rollback: delete the session and question context we just created
      try {
        await SessionDAO.deleteSession(session.id);
      } catch {
        // Best-effort rollback.
      }

      try {
        await SessionDAO.deleteBootstrapQuestionContext(questionContext.questionId);
      } catch {
        // Best-effort rollback.
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
