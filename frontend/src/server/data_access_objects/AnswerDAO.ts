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

export const AnswerDAO = {
  /**
   * Find an answer by its ID.
   * Returns null if not found.
   */
  async findById(id: string): Promise<Answer | null> {
    // Supabase: supabase.from('answers').select('*').eq('id', id).single()
    throw new Error('AnswerDAO.findById not yet wired to Supabase');
  },

  /**
   * Update an answer with partial fields.
   * Returns the updated answer entity.
   * Throws on database failure.
   */
  async update(id: string, fields: Partial<Pick<Answer, 'finalized' | 'editable' | 'status' | 'updatedAt'>>): Promise<Answer> {
    // Supabase: supabase.from('answers').update({ ...fields, updatedAt: new Date().toISOString() }).eq('id', id).select().single()
    throw new Error('AnswerDAO.update not yet wired to Supabase');
  },

  /**
   * Update the content of an answer.
   * Returns the updated answer entity.
   * Throws on database failure.
   *
   * Path: 337-prevent-edit-of-locked-answer
   */
  async updateContent(id: string, content: string): Promise<Answer> {
    // Supabase: supabase.from('answers').update({ content, updatedAt: new Date().toISOString() }).eq('id', id).select().single()
    throw new Error('AnswerDAO.updateContent not yet wired to Supabase');
  },
} as const;
