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
import { supabase } from '@/lib/supabase';
import { FinalizeSessionErrors, FinalizeSessionError } from '@/server/error_definitions/FinalizeSessionErrors';

export interface SessionForFinalization {
  id: string;
  state: string;
  requiredInputsComplete: boolean;
  responses: string[];
  createdAt: string;
  updatedAt: string;
}

export const SessionStoryRecordDAO = {
  async findSessionById(id: string): Promise<SessionForFinalization | null> {
    try {
      const { data, error } = await supabase
        .from('sessions')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw FinalizeSessionErrors.SessionPersistenceError(`Failed to find session: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        state: data.state,
        requiredInputsComplete: data.required_inputs_complete,
        responses: data.responses,
        createdAt: data.created_at,
        updatedAt: data.updated_at,
      };
    } catch (err) {
      if (err instanceof FinalizeSessionError) throw err;
      throw FinalizeSessionErrors.SessionPersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateSessionState(id: string, newState: SessionState): Promise<Session> {
    try {
      const { data, error } = await supabase
        .from('sessions')
        .update({ state: newState, updated_at: new Date().toISOString() })
        .eq('id', id)
        .select()
        .single();

      if (error) throw FinalizeSessionErrors.SessionPersistenceError(`Failed to update session state: ${error.message}`);
      if (!data) throw FinalizeSessionErrors.SessionPersistenceError('No data returned');

      return {
        id: data.id,
        state: data.state,
        requiredInputsComplete: data.required_inputs_complete,
        createdAt: data.created_at,
        updatedAt: data.updated_at,
      } as Session;
    } catch (err) {
      if (err instanceof FinalizeSessionError) throw err;
      throw FinalizeSessionErrors.SessionPersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  async upsertStoryRecord(
    sessionId: string,
    responses: string[],
    status: StoryStatus,
  ): Promise<StoryRecord> {
    try {
      const { data, error } = await supabase
        .from('story_records')
        .upsert({
          session_id: sessionId,
          responses,
          status,
        })
        .select()
        .single();

      if (error) throw FinalizeSessionErrors.StoryRecordPersistenceError(`Failed to upsert story record: ${error.message}`);
      if (!data) throw FinalizeSessionErrors.StoryRecordPersistenceError('No data returned');

      return data as StoryRecord;
    } catch (err) {
      if (err instanceof FinalizeSessionError) throw err;
      throw FinalizeSessionErrors.StoryRecordPersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
