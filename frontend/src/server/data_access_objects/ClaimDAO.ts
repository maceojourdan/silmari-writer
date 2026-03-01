/**
 * ClaimDAO - Encapsulates database operations for claim entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Paths:
 *   - 305-followup-sms-for-uncertain-claim
 *   - 321-verify-key-claims-via-voice-or-sms
 *   - 328-exclude-incomplete-claim-during-draft-generation
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { Claim, ClaimStatus, TruthCheckVerdict, CaseClaim, StoryRecordClaim, ConfirmedClaim } from '@/server/data_structures/Claim';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';

export const ClaimDAO = {
  /**
   * Find a claim by its ID.
   */
  async findById(claimId: string): Promise<Claim | null> {
    // Supabase: supabase.from('claims')
    //   .select('*')
    //   .eq('id', claimId)
    //   .single()
    throw new Error('ClaimDAO.findById not yet wired to Supabase');
  },

  /**
   * Find a claim by phone number (for webhook correlation).
   */
  async findByPhoneNumber(phoneNumber: string): Promise<Claim | null> {
    // Supabase: supabase.from('claims')
    //   .select('*')
    //   .eq('phoneNumber', phoneNumber)
    //   .eq('status', 'UNCERTAIN')
    //   .order('created_at', { ascending: false })
    //   .limit(1)
    //   .single()
    throw new Error('ClaimDAO.findByPhoneNumber not yet wired to Supabase');
  },

  /**
   * Update a claim's truth_checks array and status.
   */
  async updateTruthCheck(
    claimId: string,
    verdict: TruthCheckVerdict,
    source: string,
  ): Promise<Claim> {
    // Supabase: supabase.from('claims')
    //   .update({
    //     truth_checks: [...existing, { verdict, source, created_at }],
    //     status: verdict === 'confirmed' ? 'CONFIRMED' : 'DENIED',
    //     updated_at: new Date().toISOString(),
    //   })
    //   .eq('id', claimId)
    //   .select()
    //   .single()
    throw new Error('ClaimDAO.updateTruthCheck not yet wired to Supabase');
  },
  // -------------------------------------------------------------------------
  // Path 321: verify-key-claims-via-voice-or-sms
  // -------------------------------------------------------------------------

  /**
   * Get all unverified claim records for a session.
   * Returns claims with status 'unverified' ordered by category.
   */
  async getUnverifiedClaimsBySession(sessionId: string): Promise<ClaimRecord[]> {
    // Supabase: supabase.from('claims')
    //   .select('*')
    //   .eq('sessionId', sessionId)
    //   .eq('status', 'unverified')
    //   .order('category', { ascending: true })
    throw new Error('ClaimDAO.getUnverifiedClaimsBySession not yet wired to Supabase');
  },

  /**
   * Update claim records status to 'verified' with timestamp.
   * Wraps the update in a transaction for atomicity.
   *
   * @throws DataAccessError on failure
   */
  async updateStatusToVerified(claimIds: string[]): Promise<ClaimRecord[]> {
    // Supabase: supabase.from('claims')
    //   .update({
    //     status: 'verified',
    //     verifiedAt: new Date().toISOString(),
    //     updatedAt: new Date().toISOString(),
    //   })
    //   .in('id', claimIds)
    //   .select()
    throw new Error('ClaimDAO.updateStatusToVerified not yet wired to Supabase');
  },

  // -------------------------------------------------------------------------
  // Path 324: verification-timeout-keeps-claims-unverified-and-drafting-on-hold
  // -------------------------------------------------------------------------

  /**
   * Update a claim's status.
   *
   * @returns Updated claim entity.
   */
  async updateStatus(claimId: string, status: ClaimStatus): Promise<Claim> {
    // Supabase: supabase.from('claims')
    //   .update({ status, updated_at: new Date().toISOString() })
    //   .eq('id', claimId)
    //   .select()
    //   .single()
    throw new Error('ClaimDAO.updateStatus not yet wired to Supabase');
  },

  // -------------------------------------------------------------------------
  // Path 326: generate-draft-with-only-confirmed-claims
  // -------------------------------------------------------------------------

  /**
   * Get all claims for a case, returning them as CaseClaim entities.
   *
   * @returns Array of CaseClaim entities for the given case.
   */
  async getClaimsByCaseId(_caseId: string): Promise<CaseClaim[]> {
    // Supabase: supabase.from('claims')
    //   .select('id, caseId, text, status, metadata')
    //   .eq('caseId', caseId)
    throw new Error('ClaimDAO.getClaimsByCaseId not yet wired to Supabase');
  },

  // -------------------------------------------------------------------------
  // Path 327: prevent-draft-generation-without-confirmed-claims
  // -------------------------------------------------------------------------

  /**
   * Get all claims for a story record, returning them as StoryRecordClaim entities.
   *
   * @returns Array of StoryRecordClaim entities for the given story record.
   */
  async getClaimsByStoryRecordId(_storyRecordId: string): Promise<StoryRecordClaim[]> {
    // Supabase: supabase.from('claims')
    //   .select('id, storyRecordId, confirmed, content')
    //   .eq('storyRecordId', storyRecordId)
    throw new Error('ClaimDAO.getClaimsByStoryRecordId not yet wired to Supabase');
  },

  // -------------------------------------------------------------------------
  // Path 328: exclude-incomplete-claim-during-draft-generation
  // -------------------------------------------------------------------------

  /**
   * Get all confirmed claims for a session, including structural metadata
   * fields (metric, scope, context) for completeness evaluation.
   *
   * @returns Array of ConfirmedClaim entities with status === 'CONFIRMED'.
   */
  async getConfirmedClaims(_sessionId: string): Promise<ConfirmedClaim[]> {
    // Supabase: supabase.from('claims')
    //   .select('id, sessionId, content, status, metric, scope, context, created_at, updated_at')
    //   .eq('sessionId', sessionId)
    //   .eq('status', 'CONFIRMED')
    throw new Error('ClaimDAO.getConfirmedClaims not yet wired to Supabase');
  },
} as const;
