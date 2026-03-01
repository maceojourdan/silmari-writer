/**
 * SessionObjectVerifier - Validates structured session objects against
 * cross-layer rules using Zod schemas and backend-specific semantic rules.
 *
 * Resource: cfg-g1u4 (shared_verifier) + db-j6x9 (backend_verifier)
 * Paths:
 *   - 294-parse-and-store-session-input-objects
 *   - 312-reject-session-initialization-when-required-objects-missing-or-invalid
 */

import {
  ResumeObjectSchema,
  JobObjectSchema,
  QuestionObjectSchema,
} from '@/server/data_structures/SessionObjects';
import type { TransformedSessionInput } from '@/server/transformers/SessionInputTransformer';

export type VerificationSuccess = { valid: true };
export type VerificationFailure = { valid: false; errors: string[] };
export type VerificationResult = VerificationSuccess | VerificationFailure;

export const SessionObjectVerifier = {
  /**
   * Validate all three structured objects against their Zod schemas.
   * Returns { valid: true } or { valid: false, errors: [...] }.
   */
  validate(objects: TransformedSessionInput): VerificationResult {
    const errors: string[] = [];

    const resumeResult = ResumeObjectSchema.safeParse(objects.resume);
    if (!resumeResult.success) {
      errors.push(
        ...resumeResult.error.issues.map(
          (issue) => `resume.${issue.path.join('.')}: ${issue.message}`,
        ),
      );
    }

    const jobResult = JobObjectSchema.safeParse(objects.job);
    if (!jobResult.success) {
      errors.push(
        ...jobResult.error.issues.map(
          (issue) => `job.${issue.path.join('.')}: ${issue.message}`,
        ),
      );
    }

    const questionResult = QuestionObjectSchema.safeParse(objects.question);
    if (!questionResult.success) {
      errors.push(
        ...questionResult.error.issues.map(
          (issue) => `question.${issue.path.join('.')}: ${issue.message}`,
        ),
      );
    }

    if (errors.length > 0) {
      return { valid: false, errors };
    }

    return { valid: true };
  },

  /**
   * Verify that all required domain objects are present (not null/undefined).
   * Returns { valid: true } or { valid: false, errors: [...] } identifying
   * which object(s) are missing.
   *
   * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
   * Resource: db-j6x9 (backend_verifier)
   */
  verifyPresence(objects: {
    resume: unknown;
    job: unknown;
    question: unknown;
  }): VerificationResult {
    const errors: string[] = [];

    if (objects.resume == null) {
      errors.push('ResumeObject is required but missing');
    }

    if (objects.job == null) {
      errors.push('JobObject is required but missing');
    }

    if (objects.question == null) {
      errors.push('QuestionObject is required but missing');
    }

    if (errors.length > 0) {
      return { valid: false, errors };
    }

    return { valid: true };
  },
} as const;
