/**
 * SessionInputProcessor - Core processing unit that parses and structures
 * raw inputs using transformer + verifier, producing validated objects.
 *
 * Resource: db-b7r2 (processor)
 * Path: 294-parse-and-store-session-input-objects
 */

import type { ParsedSessionInput } from '@/server/data_structures/SessionObjects';
import { SessionInputTransformer, type RawSessionInput } from '@/server/transformers/SessionInputTransformer';
import { SessionObjectVerifier } from '@/server/verifiers/SessionObjectVerifier';
import { SessionErrors } from '@/server/error_definitions/SessionErrors';

export const SessionInputProcessor = {
  /**
   * Process raw session input:
   * 1. Transform raw input into structured objects
   * 2. Validate structured objects via shared verifier
   * 3. Return validated ParsedSessionInput
   *
   * Errors:
   * - Transformer throws → SessionErrors.ParseFailure
   * - Verifier fails → SessionErrors.ValidationFailure
   */
  async process(rawInput: RawSessionInput): Promise<ParsedSessionInput> {
    // Step 1: Transform
    let transformed;
    try {
      transformed = SessionInputTransformer.transform(rawInput);
    } catch (error) {
      throw SessionErrors.ParseFailure(
        `Failed to parse session input: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    // Step 2: Validate
    const verification = SessionObjectVerifier.validate(transformed);
    if (!verification.valid) {
      throw SessionErrors.ValidationFailure(
        `Session input validation failed: ${verification.errors.join('; ')}`,
      );
    }

    // Step 3: Return validated objects
    return {
      resume: transformed.resume,
      job: transformed.job,
      question: transformed.question,
    };
  },
} as const;
