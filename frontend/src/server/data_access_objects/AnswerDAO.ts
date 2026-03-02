/**
 * AnswerDAO - Handles database persistence for answer entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Paths:
 *   - 333-finalize-answer-locks-editing
 *   - 337-prevent-edit-of-locked-answer
 *
 * In production, each method performs Supabase queries. For TDD, methods are designed to be mockable.
 */

import type { Answer } from '@/server/data_structures/Answer';
import { supabase } from '@/lib/supabase';
import { AnswerErrors, AnswerError } from '@/server/error_definitions/AnswerErrors';

function mapAnswer(data: Record<string, unknown>): Answer {
  return {
    id: data.id as string,
    status: data.status as Answer['status'],
    finalized: data.finalized as boolean,
    editable: data.editable as boolean,
    locked: (data.locked ?? false) as boolean,
    content: data.content as string,
    userId: (data.user_id ?? data.userId) as string,
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
  };
}

export const AnswerDAO = {
  async findById(id: string): Promise<Answer | null> {
    try {
      const { data, error } = await supabase
        .from('answers')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw AnswerErrors.PersistenceError(`Failed to find answer: ${error.message}`);
      if (!data) return null;
      return mapAnswer(data);
    } catch (err) {
      if (err instanceof AnswerError) throw err;
      throw AnswerErrors.PersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  async update(id: string, fields: Partial<Pick<Answer, 'finalized' | 'editable' | 'status' | 'updatedAt'>>): Promise<Answer> {
    try {
      const updatePayload: Record<string, unknown> = {
        updated_at: new Date().toISOString(),
      };
      if (fields.finalized !== undefined) updatePayload.finalized = fields.finalized;
      if (fields.editable !== undefined) updatePayload.editable = fields.editable;
      if (fields.status !== undefined) updatePayload.status = fields.status;

      const { data, error } = await supabase
        .from('answers')
        .update(updatePayload)
        .eq('id', id)
        .select()
        .single();

      if (error) throw AnswerErrors.PersistenceError(`Failed to update answer: ${error.message}`);
      if (!data) throw AnswerErrors.PersistenceError('No data returned from answer update');
      return mapAnswer(data);
    } catch (err) {
      if (err instanceof AnswerError) throw err;
      throw AnswerErrors.PersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateContent(id: string, content: string): Promise<Answer> {
    try {
      const { data, error } = await supabase
        .from('answers')
        .update({
          content,
          updated_at: new Date().toISOString(),
        })
        .eq('id', id)
        .select()
        .single();

      if (error) throw AnswerErrors.PersistenceError(`Failed to update answer content: ${error.message}`);
      if (!data) throw AnswerErrors.PersistenceError('No data returned from answer content update');
      return mapAnswer(data);
    } catch (err) {
      if (err instanceof AnswerError) throw err;
      throw AnswerErrors.PersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
