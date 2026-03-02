/**
 * SessionDAO - Handles database persistence for session state transitions
 * and voice-assisted answer session creation.
 *
 * Resource: db-d3w8 (data_access_object)
 * Paths:
 *   - 299-approve-draft-and-transition-to-finalize
 *   - 306-initiate-voice-assisted-answer-session
 *   - 307-process-voice-input-and-progress-session
 *   - 318-complete-voice-answer-advances-workflow
 *
 * In production, each method performs Supabase queries against
 * the sessions table. For TDD, methods are designed to be mockable.
 */

import type { Session, SessionState } from '@/server/data_structures/Session';
import type { AnswerSession, AnswerSessionState, AnswerStoryRecord } from '@/server/data_structures/AnswerSession';
import type { SlotState } from '@/server/data_structures/VoiceInteractionContext';
import { supabase } from '@/lib/supabase';
import { SessionErrors, SessionError } from '@/server/error_definitions/SessionErrors';

function mapSession(data: Record<string, unknown>): Session {
  return {
    id: data.id as string,
    state: data.state as Session['state'],
    createdAt: data.created_at as string,
    updatedAt: data.updated_at as string,
  };
}

function mapAnswerSession(data: Record<string, unknown>): AnswerSession {
  return {
    id: data.id as string,
    userId: data.user_id as string,
    state: data.state as AnswerSession['state'],
    createdAt: data.created_at as string,
    updatedAt: data.updated_at as string,
  };
}

function mapStoryRecord(data: Record<string, unknown>): AnswerStoryRecord {
  return {
    id: data.id as string,
    // Voice workflow records are linked via voice_session_id.
    // Keep session_id as legacy fallback for older rows.
    sessionId: (data.voice_session_id ?? data.session_id) as string,
    status: data.status as AnswerStoryRecord['status'],
    content: data.content as string | undefined,
    createdAt: data.created_at as string,
    updatedAt: data.updated_at as string,
  };
}

export const SessionDAO = {
  /**
   * Find a session by its ID.
   * Returns null if not found.
   */
  async findById(id: string): Promise<Session | null> {
    try {
      const { data, error } = await supabase
        .from('sessions')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to find session: ${error.message}`);
      }

      if (!data) return null;
      return mapSession(data);
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Update session state and return the updated entity.
   * Throws PersistenceError on database failure.
   */
  async updateState(id: string, newState: SessionState): Promise<Session> {
    try {
      const { data, error } = await supabase
        .from('sessions')
        .update({ state: newState, updated_at: new Date().toISOString() })
        .eq('id', id)
        .select()
        .single();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to update session state: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.PersistenceFailure('No data returned from session state update');
      }
      return mapSession(data);
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  // -------------------------------------------------------------------------
  // Path 306: initiate-voice-assisted-answer-session
  // -------------------------------------------------------------------------

  /**
   * Create a new AnswerSession in INIT state.
   * Returns the persisted entity with generated ID and timestamps.
   */
  async createSession(userId: string): Promise<AnswerSession> {
    try {
      const { data, error } = await supabase
        .from('answer_sessions')
        .insert({ user_id: userId, state: 'INIT' })
        .select()
        .single();

      if (error) {
        throw SessionErrors.SessionPersistenceError(`Failed to create answer session: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.SessionPersistenceError('No data returned from answer session creation');
      }
      return mapAnswerSession(data);
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.SessionPersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Create a new StoryRecord linked to an AnswerSession in INIT status.
   * Returns the persisted entity with generated ID and timestamps.
   */
  async createStoryRecord(sessionId: string, userId: string): Promise<AnswerStoryRecord> {
    try {
      const { data, error } = await supabase
        .from('story_records')
        .insert({ voice_session_id: sessionId, user_id: userId, status: 'INIT' })
        .select()
        .single();

      if (error) {
        throw SessionErrors.StoryPersistenceError(`Failed to create story record: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.StoryPersistenceError('No data returned from story record creation');
      }
      return mapStoryRecord(data);
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.StoryPersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Delete an AnswerSession by ID (used for rollback on failure).
   */
  async deleteSession(sessionId: string): Promise<void> {
    try {
      const { error } = await supabase
        .from('answer_sessions')
        .delete()
        .eq('id', sessionId);

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to delete answer session: ${error.message}`);
      }
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  // -------------------------------------------------------------------------
  // Path 307: process-voice-input-and-progress-session
  // -------------------------------------------------------------------------

  /**
   * Find an AnswerSession by its ID.
   * Returns null if not found.
   */
  async findAnswerSessionById(id: string): Promise<AnswerSession | null> {
    try {
      const { data, error } = await supabase
        .from('answer_sessions')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to find answer session: ${error.message}`);
      }

      if (!data) return null;
      return mapAnswerSession(data);
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Find an AnswerStoryRecord by session ID.
   * Returns null if not found.
   */
  async findStoryRecordBySessionId(sessionId: string): Promise<AnswerStoryRecord | null> {
    try {
      const { data, error } = await supabase
        .from('story_records')
        .select('*')
        .eq('voice_session_id', sessionId)
        .maybeSingle();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to find story record: ${error.message}`);
      }

      if (!data) return null;
      return mapStoryRecord(data);
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Sequentially update both the AnswerSession state and AnswerStoryRecord content.
   * Returns the updated entities.
   * Throws on database failure.
   */
  async updateSessionAndStoryRecord(
    sessionId: string,
    newState: AnswerSessionState,
    storyRecordId: string,
    storyContent: string,
  ): Promise<{ session: AnswerSession; storyRecord: AnswerStoryRecord }> {
    try {
      // Step 1: Update the answer session
      const { data: sessionData, error: sessionError } = await supabase
        .from('answer_sessions')
        .update({ state: newState, updated_at: new Date().toISOString() })
        .eq('id', sessionId)
        .select()
        .single();

      if (sessionError) {
        throw SessionErrors.PersistenceFailed(`Failed to update answer session: ${sessionError.message}`);
      }
      if (!sessionData) {
        throw SessionErrors.PersistenceFailed('No data returned from answer session update');
      }

      // Step 2: Update the story record
      const { data: storyData, error: storyError } = await supabase
        .from('story_records')
        .update({ status: newState, content: storyContent, updated_at: new Date().toISOString() })
        .eq('id', storyRecordId)
        .select()
        .single();

      if (storyError) {
        throw SessionErrors.PersistenceFailed(`Failed to update story record (session already updated): ${storyError.message}`);
      }
      if (!storyData) {
        throw SessionErrors.PersistenceFailed('No data returned from story record update');
      }

      return {
        session: mapAnswerSession(sessionData),
        storyRecord: mapStoryRecord(storyData),
      };
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailed(`Unexpected: ${(err as Error).message}`);
    }
  },

  // -------------------------------------------------------------------------
  // Path 318: complete-voice-answer-advances-workflow
  // -------------------------------------------------------------------------

  /**
   * Save completed slot values for a session and question type.
   * Marks the question_type as complete.
   */
  async saveSlots(
    sessionId: string,
    questionTypeId: string,
    slotState: SlotState,
  ): Promise<void> {
    try {
      const { error } = await supabase
        .from('session_slots')
        .upsert({
          session_id: sessionId,
          question_type_id: questionTypeId,
          slots: slotState.slots,
          status: 'COMPLETE',
        });

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to save slots: ${error.message}`);
      }
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Update AnswerSession state for workflow advancement.
   */
  async updateAnswerSessionState(
    sessionId: string,
    newState: AnswerSessionState,
  ): Promise<AnswerSession> {
    try {
      const { data, error } = await supabase
        .from('answer_sessions')
        .update({ state: newState, updated_at: new Date().toISOString() })
        .eq('id', sessionId)
        .select()
        .single();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to update answer session state: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.PersistenceFailure('No data returned from answer session state update');
      }
      return mapAnswerSession(data);
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
