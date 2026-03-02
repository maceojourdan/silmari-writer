/**
 * UserDAO - Handles database persistence for user entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Paths:
 *   - 335-trigger-sms-follow-up-on-answer-finalization
 *
 * In production, each method performs Supabase queries. For TDD, methods are designed to be mockable.
 */

import type { User } from '@/server/data_structures/User';

export const UserDAO = {
  /**
   * Find a user by their ID.
   * Returns null if not found.
   */
  async findById(id: string): Promise<User | null> {
    // Supabase: supabase.from('users').select('*').eq('id', id).single()
    throw new Error('UserDAO.findById not yet wired to Supabase');
  },
} as const;
