/**
 * SessionObjectVerifier - Validates structured session objects against
 * cross-layer rules using Zod schemas.
 *
 * Resource: cfg-g1u4 (shared_verifier)
 * Path: 294-parse-and-store-session-input-objects
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
} as const;
