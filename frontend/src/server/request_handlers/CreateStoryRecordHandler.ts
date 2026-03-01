/**
 * CreateStoryRecordHandler - Orchestrates the ORIENT story record creation flow
 * by composing process chain → verifier → DAO.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 295-orient-state-creates-single-story-record
 */

import type { OrientEvent, OrientStoryRecord } from '@/server/data_structures/OrientStoryRecord';
import { OrientProcessChain } from '@/server/process_chains/OrientProcessChain';
import { StoryRecordVerifier } from '@/server/verifiers/StoryRecordVerifier';
import { OrientStoryRecordDAO } from '@/server/data_access_objects/OrientStoryRecordDAO';
import { OrientError } from '@/server/error_definitions/OrientErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export const CreateStoryRecordHandler = {
  /**
   * Handle the full ORIENT story record creation flow:
   * 1. Start ORIENT process chain
   * 2. Select experience and derive story data
   * 3. Validate story record structure
   * 4. Persist story record
   *
   * Known errors (OrientError) are rethrown as-is.
   * Unknown errors are logged and wrapped in GenericErrors.InternalError.
   */
  async handle(event: OrientEvent): Promise<OrientStoryRecord> {
    try {
      // Step 1: Trigger ORIENT process chain
      const context = OrientProcessChain.startOrientProcess(event);

      // Step 2: Select single experience and derive story data
      const payload = OrientProcessChain.selectExperience(context);

      // Step 3: Validate StoryRecord structure
      const validatedRecord = StoryRecordVerifier.validateStoryRecord(payload);

      // Step 4: Persist StoryRecord
      const persistedRecord = await OrientStoryRecordDAO.insertStoryRecord(validatedRecord);

      return persistedRecord;
    } catch (error) {
      // Known orient errors → rethrow
      if (error instanceof OrientError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during story record creation',
        error,
        { path: '295-orient-state-creates-single-story-record', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during story record creation: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
