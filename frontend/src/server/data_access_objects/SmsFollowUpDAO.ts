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
import { supabase } from '@/lib/supabase';
import { SmsFollowUpErrors, SmsError } from '@/server/error_definitions/SmsErrors';

export const SmsFollowUpDAO = {
  async insert(record: Omit<SmsFollowUpRecord, 'id'>): Promise<SmsFollowUpRecord> {
    try {
      const { data: row, error } = await supabase
        .from('sms_follow_ups')
        .insert({
          answer_id: record.answerId,
          phone_number: record.phoneNumber,
          message: record.message,
          status: record.status,
          message_id: record.messageId,
          created_at: record.createdAt,
        })
        .select()
        .single();

      if (error) throw SmsFollowUpErrors.PERSISTENCE_FAILURE(`Failed to insert SMS follow-up: ${error.message}`);
      if (!row) throw SmsFollowUpErrors.PERSISTENCE_FAILURE('No data returned');

      return {
        id: row.id,
        answerId: row.answer_id,
        phoneNumber: row.phone_number,
        message: row.message,
        status: row.status,
        messageId: row.message_id,
        createdAt: row.created_at,
      } as SmsFollowUpRecord;
    } catch (err) {
      if (err instanceof SmsError) throw err;
      throw SmsFollowUpErrors.PERSISTENCE_FAILURE(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
