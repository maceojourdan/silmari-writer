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

export const VerificationDAO = {
  /**
   * Retrieve a claimant by their unique identifier.
   * Returns null if not found.
   */
  async getClaimantById(claimantId: string): Promise<Claimant | null> {
    // Supabase: supabase.from('claimants')
    //   .select('id, key_claims, phone, sms_opt_in')
    //   .eq('id', claimantId)
    //   .single()
    throw new Error('VerificationDAO.getClaimantById not yet wired to Supabase');
  },

  /**
   * Create a new verification attempt record.
   */
  async createVerificationAttempt(
    claimantId: string,
    status: string,
    reason: string,
  ): Promise<VerificationAttempt> {
    // Supabase: supabase.from('verification_attempts')
    //   .insert({ claimantId, status, reason })
    //   .select()
    //   .single()
    throw new Error('VerificationDAO.createVerificationAttempt not yet wired to Supabase');
  },

  /**
   * Get the latest verification attempt for a claimant.
   */
  async getLatestVerificationAttempt(
    claimantId: string,
  ): Promise<VerificationAttempt | null> {
    // Supabase: supabase.from('verification_attempts')
    //   .select('*')
    //   .eq('claimantId', claimantId)
    //   .order('createdAt', { ascending: false })
    //   .limit(1)
    //   .single()
    throw new Error('VerificationDAO.getLatestVerificationAttempt not yet wired to Supabase');
  },

  /**
   * Update the drafting status on a verification attempt.
   */
  async updateDraftingStatus(
    attemptId: string,
    draftingStatus: DraftingStatus,
  ): Promise<void> {
    // Supabase: supabase.from('verification_attempts')
    //   .update({ draftingStatus, updatedAt: new Date().toISOString() })
    //   .eq('id', attemptId)
    throw new Error('VerificationDAO.updateDraftingStatus not yet wired to Supabase');
  },
} as const;
