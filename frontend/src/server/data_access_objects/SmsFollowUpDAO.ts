/**
 * SmsFollowUpDAO - Handles database persistence for SMS follow-up records.
 *
 * Resource: db-d3w8 (data_access_object)
 * Paths:
 *   - 335-trigger-sms-follow-up-on-answer-finalization
 *
 * In production, each method performs Supabase queries. For TDD, methods are designed to be mockable.
 */

import type { SmsFollowUpRecord } from '@/server/data_structures/SmsFollowUpRecord';

export const SmsFollowUpDAO = {
  /**
   * Insert a new SMS follow-up record.
   * Returns the stored record.
   * Throws on database failure.
   */
  async insert(record: Omit<SmsFollowUpRecord, 'id'>): Promise<SmsFollowUpRecord> {
    // Supabase: supabase.from('sms_follow_ups').insert(record).select().single()
    throw new Error('SmsFollowUpDAO.insert not yet wired to Supabase');
  },
} as const;
