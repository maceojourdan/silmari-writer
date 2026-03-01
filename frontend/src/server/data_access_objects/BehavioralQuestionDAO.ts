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

export const BehavioralQuestionDAO = {
  async updateStatus(
    id: string,
    status: BehavioralQuestionStatus,
  ): Promise<BehavioralQuestion> {
    // Supabase: supabase.from('behavioral_questions')
    //   .update({ status, updated_at: new Date().toISOString() })
    //   .eq('id', id)
    //   .select()
    //   .single()
    throw new Error('BehavioralQuestionDAO.updateStatus not yet wired to Supabase');
  },

  async insert(
    entity: Omit<BehavioralQuestion, 'id' | 'createdAt' | 'updatedAt'>,
  ): Promise<BehavioralQuestion> {
    // Supabase: supabase.from('behavioral_questions')
    //   .insert(entity)
    //   .select()
    //   .single()
    throw new Error('BehavioralQuestionDAO.insert not yet wired to Supabase');
  },

  async findById(id: string): Promise<BehavioralQuestion | null> {
    // Supabase: supabase.from('behavioral_questions')
    //   .select('*')
    //   .eq('id', id)
    //   .single()
    throw new Error('BehavioralQuestionDAO.findById not yet wired to Supabase');
  },
} as const;
