/**
 * BehavioralQuestionDAO - Encapsulates database operations for
 * behavioral question entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { BehavioralQuestion, BehavioralQuestionStatus } from '@/server/data_structures/BehavioralQuestion';
import { supabase } from '@/lib/supabase';
import { BehavioralQuestionErrors, BehavioralQuestionError } from '@/server/error_definitions/BehavioralQuestionErrors';

function mapBehavioralQuestion(data: Record<string, unknown>): BehavioralQuestion {
  return {
    id: data.id as string,
    sessionId: data.session_id as string,
    objective: data.objective as string,
    actions: data.actions as string[],
    obstacles: data.obstacles as string[],
    outcome: data.outcome as string,
    roleClarity: data.role_clarity as string,
    status: data.status as BehavioralQuestionStatus,
    createdAt: data.created_at as string,
    updatedAt: data.updated_at as string,
  };
}

export const BehavioralQuestionDAO = {
  async updateStatus(
    id: string,
    status: BehavioralQuestionStatus,
  ): Promise<BehavioralQuestion> {
    try {
      const { data, error } = await supabase
        .from('behavioral_questions')
        .update({ status, updated_at: new Date().toISOString() })
        .eq('id', id)
        .select()
        .single();

      if (error) throw BehavioralQuestionErrors.PERSISTENCE_FAILED(`Failed to update status: ${error.message}`);
      if (!data) throw BehavioralQuestionErrors.PERSISTENCE_FAILED('No data returned');

      return mapBehavioralQuestion(data);
    } catch (err) {
      if (err instanceof BehavioralQuestionError) throw err;
      throw BehavioralQuestionErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async insert(
    entity: Omit<BehavioralQuestion, 'id' | 'createdAt' | 'updatedAt'>,
  ): Promise<BehavioralQuestion> {
    try {
      const { data, error } = await supabase
        .from('behavioral_questions')
        .insert({
          objective: entity.objective,
          actions: entity.actions,
          obstacles: entity.obstacles,
          outcome: entity.outcome,
          role_clarity: entity.roleClarity,
          status: entity.status,
          session_id: entity.sessionId,
        })
        .select()
        .single();

      if (error) throw BehavioralQuestionErrors.PERSISTENCE_FAILED(`Failed to insert: ${error.message}`);
      if (!data) throw BehavioralQuestionErrors.PERSISTENCE_FAILED('No data returned');

      return mapBehavioralQuestion(data);
    } catch (err) {
      if (err instanceof BehavioralQuestionError) throw err;
      throw BehavioralQuestionErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findById(id: string): Promise<BehavioralQuestion | null> {
    try {
      const { data, error } = await supabase
        .from('behavioral_questions')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw BehavioralQuestionErrors.PERSISTENCE_FAILED(`Failed to find: ${error.message}`);
      if (!data) return null;

      return mapBehavioralQuestion(data);
    } catch (err) {
      if (err instanceof BehavioralQuestionError) throw err;
      throw BehavioralQuestionErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
