/**
 * DraftProcessChain - Triggers and sequences DRAFT state execution.
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import type { DraftExecutionContext } from '@/server/data_structures/DraftStoryRecord';
import { StoryRecordDAO } from '@/server/data_access_objects/StoryRecordDAO';
import {
  DraftStateError,
} from '@/server/error_definitions/DraftErrors';

export const DraftProcessChain = {
  /**
   * Step 1: Trigger DRAFT execution.
   *
   * Validates that the StoryRecord exists and is in DRAFT state,
   * then returns the execution context containing the record and truth_checks.
   */
  async execute(storyRecordId: string): Promise<DraftExecutionContext> {
    const storyRecord = await StoryRecordDAO.findById(storyRecordId);

    if (!storyRecord) {
      throw DraftStateError.STORY_NOT_FOUND(
        `StoryRecord '${storyRecordId}' not found`,
      );
    }

    if (storyRecord.status !== 'DRAFT') {
      throw DraftStateError.INVALID_STATE(
        `StoryRecord '${storyRecordId}' is in '${storyRecord.status}' state, expected 'DRAFT'`,
      );
    }

    return {
      storyRecordId,
      storyRecord,
    };
  },
} as const;
