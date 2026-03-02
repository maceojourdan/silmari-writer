/**
 * VerificationDAO - Encapsulates database operations for claimant
 * and verification attempt entities in Path 323.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 323-fail-verification-when-no-contact-method
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { Claimant } from '@/server/data_structures/Claimant';
import type { VerificationAttempt } from '@/server/data_structures/VerificationAttempt';
import type { DraftingStatus } from '@/server/data_structures/VerificationAttempt';
import { supabase } from '@/lib/supabase';
import { VerificationErrors, VerificationError } from '@/server/error_definitions/VerificationErrors';

export const VerificationDAO = {
  async getClaimantById(claimantId: string): Promise<Claimant | null> {
    try {
      const { data, error } = await supabase
        .from('claimants')
        .select('id, key_claims, phone, sms_opt_in')
        .eq('id', claimantId)
        .maybeSingle();

      if (error) throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to get claimant: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        keyClaims: data.key_claims,
        phone: data.phone,
        smsOptIn: data.sms_opt_in,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async createVerificationAttempt(
    claimantId: string,
    status: string,
    reason: string,
  ): Promise<VerificationAttempt> {
    try {
      const { data, error } = await supabase
        .from('verification_attempts')
        .insert({
          claimant_id: claimantId,
          status,
          reason,
        })
        .select()
        .single();

      if (error) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Failed to create verification attempt: ${error.message}`);
      if (!data) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED('No data returned from insert');

      return {
        id: data.id,
        claimantId: data.claimant_id,
        status: data.status,
        reason: data.reason,
        draftingStatus: data.drafting_status,
        createdAt: data.created_at,
        updatedAt: data.updated_at,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async getLatestVerificationAttempt(
    claimantId: string,
  ): Promise<VerificationAttempt | null> {
    try {
      const { data, error } = await supabase
        .from('verification_attempts')
        .select('*')
        .eq('id', claimantId)
        .order('created_at', { ascending: false })
        .limit(1)
        .single();

      if (error) {
        if (error.code === 'PGRST116') return null;
        throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to get latest attempt: ${error.message}`);
      }

      if (!data) return null;

      return {
        id: data.id,
        claimantId: data.claimant_id,
        status: data.status,
        reason: data.reason,
        draftingStatus: data.drafting_status,
        createdAt: data.created_at,
        updatedAt: data.updated_at,
      };
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateDraftingStatus(
    attemptId: string,
    draftingStatus: DraftingStatus,
  ): Promise<void> {
    try {
      const { error } = await supabase
        .from('verification_attempts')
        .update({
          drafting_status: draftingStatus,
          updated_at: new Date().toISOString(),
        })
        .eq('id', attemptId);

      if (error) throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Failed to update drafting status: ${error.message}`);
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
