/**
 * SessionInitService - Orchestrates persistence of session initialization objects.
 *
 * Resource: db-h2s4 (service)
 * Path: 294-parse-and-store-session-input-objects
 *
 * Uses sequential inserts to simulate transactional semantics.
 * In production, this would use Supabase rpc or explicit transaction wrapper.
 * If any step fails, a PERSISTENCE_FAILURE error is thrown (the caller can retry).
 */

import type {
  ParsedSessionInput,
  SessionInitResult,
} from '@/server/data_structures/SessionObjects';
import { SessionInitDAO } from '@/server/data_access_objects/SessionInitDAO';
import { SessionErrors } from '@/server/error_definitions/SessionErrors';

export const SessionInitService = {
  /**
   * Persist the full session initialization package:
   * 1. Insert resume → get resumeId
   * 2. Insert job → get jobId
   * 3. Insert question → get questionId
   * 4. Insert session (linking all three) → get sessionId
   *
   * On failure at any step, throw PERSISTENCE_FAILURE.
   */
  async initialize(input: ParsedSessionInput): Promise<SessionInitResult> {
    let resumeId: string;
    let jobId: string;
    let questionId: string;
    let sessionId: string;

    // Step 1: Insert Resume
    try {
      resumeId = await SessionInitDAO.insertResume(input.resume);
    } catch (error) {
      throw SessionErrors.PersistenceFailure(
        `Failed to insert resume: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    // Step 2: Insert Job
    try {
      jobId = await SessionInitDAO.insertJob(input.job);
    } catch (error) {
      throw SessionErrors.PersistenceFailure(
        `Failed to insert job: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    // Step 3: Insert Question
    try {
      questionId = await SessionInitDAO.insertQuestion(input.question);
    } catch (error) {
      throw SessionErrors.PersistenceFailure(
        `Failed to insert question: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    // Step 4: Insert Session (linking all three)
    try {
      sessionId = await SessionInitDAO.insertSession({
        resumeId,
        jobId,
        questionId,
        status: 'INITIALIZED',
      });
    } catch (error) {
      throw SessionErrors.PersistenceFailure(
        `Failed to insert session: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    return {
      sessionId,
      resumeId,
      jobId,
      questionId,
    };
  },
} as const;
