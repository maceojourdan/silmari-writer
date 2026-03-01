/**
 * OrientStoryRecordDAO - Handles persistence of OrientStoryRecord entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 295-orient-state-creates-single-story-record
 *
 * In production, performs Supabase queries against orient_story_records table.
 * For TDD, methods are designed to be mockable.
 */

import type { OrientStoryRecord } from '@/server/data_structures/OrientStoryRecord';
import { OrientErrors } from '@/server/error_definitions/OrientErrors';
import { supabase } from '@/lib/supabase';

export const OrientStoryRecordDAO = {
  /**
   * Insert exactly one new OrientStoryRecord into the database.
   *
   * Uses Supabase `.insert().select().single()` to insert and return
   * the persisted record with its generated id.
   *
   * On failure, wraps database errors into OrientError with code
   * STORY_RECORD_PERSISTENCE_FAILED.
   */
  async insertStoryRecord(record: OrientStoryRecord): Promise<OrientStoryRecord> {
    const { data, error } = await supabase
      .from('orient_story_records')
      .insert({
        story_title: record.story_title,
        initial_context: record.initial_context,
      })
      .select()
      .single();

    if (error) {
      throw OrientErrors.StoryRecordPersistenceFailed(
        `Failed to persist story record: ${error.message}`,
      );
    }

    if (!data) {
      throw OrientErrors.StoryRecordPersistenceFailed(
        'Failed to persist story record: no data returned',
      );
    }

    return data as OrientStoryRecord;
  },
} as const;
