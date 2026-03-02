/**
 * VerificationRequestDAO - Encapsulates database operations for
 * verification request entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 321-verify-key-claims-via-voice-or-sms
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type {
  VerificationRequest,
  VerificationRequestStatus,
  DeliveryAttempt,
} from '@/server/data_structures/VerificationRequest';
import { supabase } from '@/lib/supabase';
import { VerificationErrors, VerificationError } from '@/server/error_definitions/VerificationErrors';

export const VerificationRequestDAO = {
  async create(data: {
    sessionId: string;
    claimIds: string[];
    contactPhone: string;
    contactMethod: 'sms' | 'voice';
    token: string;
  }): Promise<VerificationRequest> {
    try {
      const { data: row, error } = await supabase
        .from('verification_requests')
        .insert({
          session_id: data.sessionId,
          claim_ids: data.claimIds,
          contact_phone: data.contactPhone,
          contact_method: data.contactMethod,
          token: data.token,
          status: 'pending',
          attempt_count: 0,
        })
        .select()
        .single();

      if (error) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Failed to create request: ${error.message}`);
      if (!row) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED('No data returned');

      return {
        id: row.id,
        sessionId: row.session_id,
        status: row.status,
        attemptCount: row.attempt_count,
        token: row.token,
        claimIds: row.claim_ids,
        contactPhone: row.contact_phone,
        contactMethod: row.contact_method,
        createdAt: row.created_at,
        respondedAt: row.responded_at,
        updatedAt: row.updated_at,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findByToken(token: string): Promise<VerificationRequest | null> {
    try {
      const { data, error } = await supabase
        .from('verification_requests')
        .select('*')
        .eq('token', token)
        .eq('status', 'pending')
        .maybeSingle();

      if (error) throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to find by token: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        sessionId: data.session_id,
        status: data.status,
        attemptCount: data.attempt_count,
        token: data.token,
        claimIds: data.claim_ids,
        contactPhone: data.contact_phone,
        contactMethod: data.contact_method,
        createdAt: data.created_at,
        respondedAt: data.responded_at,
        updatedAt: data.updated_at,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findBySessionId(sessionId: string): Promise<VerificationRequest | null> {
    try {
      const { data, error } = await supabase
        .from('verification_requests')
        .select('*')
        .eq('session_id', sessionId)
        .order('created_at', { ascending: false })
        .limit(1)
        .single();

      if (error) {
        if (error.code === 'PGRST116') return null;
        throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to find by session: ${error.message}`);
      }
      if (!data) return null;

      return {
        id: data.id,
        sessionId: data.session_id,
        status: data.status,
        attemptCount: data.attempt_count,
        token: data.token,
        claimIds: data.claim_ids,
        contactPhone: data.contact_phone,
        contactMethod: data.contact_method,
        createdAt: data.created_at,
        respondedAt: data.responded_at,
        updatedAt: data.updated_at,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatus(
    requestId: string,
    status: VerificationRequestStatus,
    attemptCount?: number,
  ): Promise<VerificationRequest> {
    try {
      const updateFields: Record<string, unknown> = {
        status,
        updated_at: new Date().toISOString(),
      };
      if (attemptCount !== undefined) {
        updateFields.attempt_count = attemptCount;
      }

      const { data, error } = await supabase
        .from('verification_requests')
        .update(updateFields)
        .eq('id', requestId)
        .select()
        .single();

      if (error) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Failed to update status: ${error.message}`);
      if (!data) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED('No data returned');

      return {
        id: data.id,
        sessionId: data.session_id,
        status: data.status,
        attemptCount: data.attempt_count,
        token: data.token,
        claimIds: data.claim_ids,
        contactPhone: data.contact_phone,
        contactMethod: data.contact_method,
        createdAt: data.created_at,
        respondedAt: data.responded_at,
        updatedAt: data.updated_at,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async logDeliveryAttempt(data: {
    requestId: string;
    attemptNumber: number;
    status: 'success' | 'failed';
    externalId?: string;
    errorMessage?: string;
  }): Promise<DeliveryAttempt> {
    try {
      const { data: row, error } = await supabase
        .from('delivery_attempts')
        .insert({
          request_id: data.requestId,
          attempt_number: data.attemptNumber,
          status: data.status,
          external_id: data.externalId,
          error_message: data.errorMessage,
        })
        .select()
        .single();

      if (error) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Failed to log delivery attempt: ${error.message}`);
      if (!row) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED('No data returned');

      return {
        id: row.id,
        requestId: row.request_id,
        attemptNumber: row.attempt_number,
        status: row.status,
        externalId: row.external_id,
        errorMessage: row.error_message,
        createdAt: row.created_at,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findPendingUnresponded(): Promise<VerificationRequest[]> {
    try {
      const { data, error } = await supabase
        .from('verification_requests')
        .select('*')
        .eq('status', 'pending')
        .is('responded_at', null);

      if (error) throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to find pending: ${error.message}`);

      return (data ?? []).map((row: Record<string, unknown>) => ({
        id: row.id as string,
        sessionId: row.session_id as string,
        status: row.status as string,
        attemptCount: row.attempt_count as number,
        token: row.token as string,
        claimIds: row.claim_ids as string[],
        contactPhone: row.contact_phone as string,
        contactMethod: row.contact_method as string,
        createdAt: row.created_at as string,
        respondedAt: (row.responded_at as string) ?? null,
        updatedAt: row.updated_at as string,
      })) as VerificationRequest[];
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatusIfUnresponded(
    requestId: string,
    newStatus: VerificationRequestStatus,
  ): Promise<number> {
    try {
      const { count, error } = await supabase
        .from('verification_requests')
        .update({
          status: newStatus,
          updated_at: new Date().toISOString(),
        })
        .eq('id', requestId)
        .is('responded_at', null);

      if (error) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Failed to update status: ${error.message}`);

      return count ?? 0;
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
