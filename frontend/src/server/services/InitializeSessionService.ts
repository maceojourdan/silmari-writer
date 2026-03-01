/**
 * InitializeSessionService - Constructs a new session entity with embedded
 * ResumeObject, JobObject, and QuestionObject, sets state to "initialized",
 * and delegates persistence to the DAO.
 *
 * Resource: db-h2s4 (service)
 * Paths:
 *   - 310-initialize-new-session-with-provided-objects
 *   - 311-reject-duplicate-session-initialization
 */

import type { ResumeObject, JobObject, QuestionObject } from '@/server/data_structures/SessionObjects';
import type { InitializedSession } from '@/server/data_structures/InitializedSession';
import { InitializeSessionDAO } from '@/server/data_access_objects/InitializeSessionDAO';
import { SessionUniquenessVerifier } from '@/server/verifiers/SessionUniquenessVerifier';
import { SessionError, SessionErrors } from '@/server/error_definitions/SessionErrors';

interface CreateSessionInput {
  resume: ResumeObject;
  job: JobObject;
  question: QuestionObject;
}

export const InitializeSessionService = {
  /**
   * Create a new session entity:
   * 1. Check if an active session already exists (Path 311)
   * 2. Verify uniqueness constraint — reject if active session found
   * 3. Construct session with embedded objects, state = "initialized"
   * 4. Delegate persistence to InitializeSessionDAO
   * 5. Return persisted session
   *
   * Known SessionErrors (e.g., PERSISTENCE_FAILURE, SESSION_ALREADY_ACTIVE)
   * are rethrown as-is.
   * Unknown errors are wrapped in SessionErrors.ServiceError.
   */
  async createSession(input: CreateSessionInput): Promise<InitializedSession> {
    try {
      // Step 1 (Path 311): Check for existing active session
      const activeSession = await InitializeSessionDAO.getActiveSession();

      // Step 2 (Path 311): Verify uniqueness — throws SESSION_ALREADY_ACTIVE if active
      SessionUniquenessVerifier.verify(activeSession !== null);

      // Step 3: Construct the session entity
      const sessionEntity = {
        resume: input.resume,
        job: input.job,
        question: input.question,
        state: 'initialized' as const,
        createdAt: new Date().toISOString(),
      };

      // Step 4: Delegate persistence to DAO
      const persisted = await InitializeSessionDAO.persist(sessionEntity);

      return persisted;
    } catch (error) {
      // Known session errors → rethrow
      if (error instanceof SessionError) {
        throw error;
      }

      // Unknown errors → wrap in ServiceError
      throw SessionErrors.ServiceError(
        `Failed to create session: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },
} as const;
