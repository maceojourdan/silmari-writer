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
import { supabase } from '@/lib/supabase';
import { SharedErrors, SharedError } from '@/server/error_definitions/SharedErrors';

export const UserDAO = {
  async findById(id: string): Promise<User | null> {
    try {
      const { data, error } = await supabase
        .from('users')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw SharedErrors.NetworkError(`Failed to find user: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        smsOptIn: data.sms_opt_in,
        phoneNumber: data.phone_number,
        createdAt: data.created_at,
        updatedAt: data.updated_at,
      } as User;
    } catch (err) {
      if (err instanceof SharedError) throw err;
      throw SharedErrors.NetworkError(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
