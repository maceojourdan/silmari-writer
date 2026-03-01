/**
 * ObjectSchemaVerifier - Cross-layer structural validation of session
 * initialization objects using Zod schemas.
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Validates that ResumeObject, JobObject, and QuestionObject conform to
 * their Zod schemas. Returns aggregated errors with object-level prefixes
 * so callers know which object failed and why.
 */

import {
  ResumeObjectSchema,
  JobObjectSchema,
  QuestionObjectSchema,
} from '@/server/data_structures/SessionObjects';

export type VerificationSuccess = { valid: true };
export type VerificationFailure = { valid: false; errors: string[] };
export type VerificationResult = VerificationSuccess | VerificationFailure;

interface ObjectsToValidate {
  resume: unknown;
  job: unknown;
  question: unknown;
}

export const ObjectSchemaVerifier = {
  /**
   * Validate all three session objects against their Zod schemas.
   * Returns { valid: true } or { valid: false, errors: [...] }.
   *
   * Error messages are prefixed with the object name for clear identification:
   *   e.g., "resume.content: Resume content is required"
   */
  validate(objects: ObjectsToValidate): VerificationResult {
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
} as const;
