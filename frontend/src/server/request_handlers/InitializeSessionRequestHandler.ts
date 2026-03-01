/**
 * InitializeSessionRequestHandler - Validates structured session input objects
 * and delegates session creation to InitializeSessionService.
 *
 * Resource: api-n8k2 (request_handler)
 * Paths:
 *   - 310-initialize-new-session-with-provided-objects
 *   - 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Unlike the Path 294 handler (which processes raw text), this handler
 * receives pre-structured ResumeObject, JobObject, QuestionObject and
 * validates them against their Zod schemas before creating the session.
 */

import type { InitializedSession } from '@/server/data_structures/InitializedSession';
import type { ResumeObject, JobObject, QuestionObject } from '@/server/data_structures/SessionObjects';
import {
  ResumeObjectSchema,
  JobObjectSchema,
  QuestionObjectSchema,
} from '@/server/data_structures/SessionObjects';
import { InitializeSessionService } from '@/server/services/InitializeSessionService';
import { SessionError, SessionErrors } from '@/server/error_definitions/SessionErrors';
import { logger } from '@/server/logging/logger';

interface InitializeSessionPayload {
  resume: ResumeObject;
  job: JobObject;
  question: QuestionObject;
}

export const InitializeSessionRequestHandler = {
  /**
   * Handle session initialization:
   * 1. Validate ResumeObject, JobObject, QuestionObject against schemas
   * 2. Delegate to InitializeSessionService.createSession
   * 3. Return InitializedSession
   *
   * Known errors (SessionError) are rethrown.
   * Unknown errors are logged and mapped to SERVICE_INVOCATION_FAILED (Path 312).
   */
  async handle(payload: InitializeSessionPayload): Promise<InitializedSession> {
    // Step 1: Validate objects against schemas
    const errors: string[] = [];

    const resumeResult = ResumeObjectSchema.safeParse(payload.resume);
    if (!resumeResult.success) {
      errors.push(
        ...resumeResult.error.issues.map(
          (issue) => `resume.${issue.path.join('.')}: ${issue.message}`,
        ),
      );
    }

    const jobResult = JobObjectSchema.safeParse(payload.job);
    if (!jobResult.success) {
      errors.push(
        ...jobResult.error.issues.map(
          (issue) => `job.${issue.path.join('.')}: ${issue.message}`,
        ),
      );
    }

    const questionResult = QuestionObjectSchema.safeParse(payload.question);
    if (!questionResult.success) {
      errors.push(
        ...questionResult.error.issues.map(
          (issue) => `question.${issue.path.join('.')}: ${issue.message}`,
        ),
      );
    }

    if (errors.length > 0) {
      throw SessionErrors.ValidationFailure(
        `Validation failed: ${errors.join('; ')}`,
      );
    }

    // Step 2: Delegate to service
    try {
      const session = await InitializeSessionService.createSession({
        resume: payload.resume,
        job: payload.job,
        question: payload.question,
      });

      return session;
    } catch (error) {
      // Known session errors → rethrow
      if (error instanceof SessionError) {
        throw error;
      }

      // Unknown errors → log and map to SERVICE_INVOCATION_FAILED (Path 312)
      logger.error(
        'Service invocation failed during session initialization',
        error,
        { path: '312-reject-session-initialization-when-required-objects-missing-or-invalid', resource: 'api-n8k2' },
      );

      throw SessionErrors.ServiceInvocationFailed(
        `Failed to invoke session initialization service: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
