/**
 * SessionStoryRecordDAO - Handles database persistence for session finalization
 * and StoryRecord upsert operations.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { Session, SessionState } from '@/server/data_structures/Session';
import type { StoryRecord, StoryStatus } from '@/server/data_structures/StoryRecord';

export interface SessionForFinalization {
  id: string;
  state: string;
  requiredInputsComplete: boolean;
  responses: string[];
  createdAt: string;
  updatedAt: string;
}

export const SessionStoryRecordDAO = {
  /**
   * Find a session by its ID, including finalization metadata.
   * Returns null if not found.
   */
  async findSessionById(id: string): Promise<SessionForFinalization | null> {
    // Supabase: supabase.from('sessions').select('*').eq('id', id).single()
    throw new Error('SessionStoryRecordDAO.findSessionById not yet wired to Supabase');
  },

  /**
   * Update session state to the given new state.
   * Returns the updated session.
   * Throws on database failure.
   */
  async updateSessionState(id: string, newState: SessionState): Promise<Session> {
    // Supabase: supabase.from('sessions').update({ state: newState, updatedAt: now() }).eq('id', id).select().single()
    throw new Error('SessionStoryRecordDAO.updateSessionState not yet wired to Supabase');
  },

  /**
   * Create or update a StoryRecord for the given session.
   * Sets status and stores responses.
   * Returns the persisted StoryRecord.
   * Throws on database failure.
   */
  async upsertStoryRecord(
    sessionId: string,
    responses: string[],
    status: StoryStatus,
  ): Promise<StoryRecord> {
    // Supabase: supabase.from('story_records').upsert({ sessionId, responses, status }).select().single()
    throw new Error('SessionStoryRecordDAO.upsertStoryRecord not yet wired to Supabase');
  },
} as const;
