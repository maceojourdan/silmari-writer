/**
 * StoryRecordDAO - Encapsulates database operations for StoryRecord
 * entities in the draft state path.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { DraftStoryRecord, DraftPayload } from '@/server/data_structures/DraftStoryRecord';
import { supabase } from '@/lib/supabase';
import { PersistenceError, PersistenceErrors } from '@/server/error_definitions/PersistenceErrors';

export const StoryRecordDAO = {
  async findById(id: string): Promise<DraftStoryRecord | null> {
    try {
      const { data, error } = await supabase
        .from('story_records')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw PersistenceErrors.UpdateFailed(`Failed to find story record: ${error.message}`);
      if (!data) return null;

      return data as DraftStoryRecord;
    } catch (err) {
      if (err instanceof PersistenceError) throw err;
      throw PersistenceErrors.UpdateFailed(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateDraft(id: string, payload: DraftPayload): Promise<DraftStoryRecord> {
    try {
      const { data, error } = await supabase
        .from('story_records')
        .update({
          draft_text: payload.draft_text,
          claims_used: payload.claims_used,
        })
        .eq('id', id)
        .select()
        .single();

      if (error) throw PersistenceErrors.UpdateFailed(`Failed to update draft: ${error.message}`);
      if (!data) throw PersistenceErrors.UpdateFailed('No data returned from update');

      return data as DraftStoryRecord;
    } catch (err) {
      if (err instanceof PersistenceError) throw err;
      throw PersistenceErrors.UpdateFailed(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
