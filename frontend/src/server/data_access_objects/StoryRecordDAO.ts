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

export const StoryRecordDAO = {
  async findById(_id: string): Promise<DraftStoryRecord | null> {
    // Supabase: supabase.from('story_records').select('*').eq('id', id).single()
    throw new Error('StoryRecordDAO.findById not yet wired to Supabase');
  },

  async updateDraft(_id: string, _payload: DraftPayload): Promise<DraftStoryRecord> {
    // Supabase: supabase.from('story_records').update({ draft_text, claims_used }).eq('id', id)
    throw new Error('StoryRecordDAO.updateDraft not yet wired to Supabase');
  },
} as const;
