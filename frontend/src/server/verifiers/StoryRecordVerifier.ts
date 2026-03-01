/**
 * StoryRecordVerifier - Validates StoryCreationPayload against the
 * OrientStoryRecord schema using Zod.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 295-orient-state-creates-single-story-record
 */

import {
  OrientStoryRecordSchema,
  type StoryCreationPayload,
  type OrientStoryRecord,
} from '@/server/data_structures/OrientStoryRecord';
import { OrientErrors } from '@/server/error_definitions/OrientErrors';

export const StoryRecordVerifier = {
  /**
   * Validate a story creation payload and return a validated OrientStoryRecord.
   *
   * Uses Zod `.parse()` to enforce required fields and structural constraints.
   * On failure, wraps the Zod error into OrientError with code
   * STORY_RECORD_VALIDATION_FAILED.
   */
  validateStoryRecord(payload: StoryCreationPayload): OrientStoryRecord {
    try {
      return OrientStoryRecordSchema.parse({
        story_title: payload.story_title,
        initial_context: payload.initial_context,
      });
    } catch (error) {
      const message =
        error instanceof Error ? error.message : 'Unknown validation error';

      throw OrientErrors.StoryRecordValidationFailed(
        `Story record validation failed: ${message}`,
      );
    }
  },
} as const;
