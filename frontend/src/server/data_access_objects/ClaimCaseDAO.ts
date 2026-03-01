/**
 * ClaimCaseDAO - Encapsulates database operations for claim dispute
 * and case drafting status management.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 322-handle-disputed-claims-and-block-drafting
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';
import type { Case } from '@/server/data_structures/Case';

export const ClaimCaseDAO = {
  /**
   * Find a claim record by its ID.
   */
  async getClaimById(claimId: string): Promise<ClaimRecord | null> {
    // Supabase: supabase.from('claims')
    //   .select('*')
    //   .eq('id', claimId)
    //   .single()
    throw new Error('ClaimCaseDAO.getClaimById not yet wired to Supabase');
  },

  /**
   * Update a claim's verification status to 'not_verified' with dispute metadata.
   */
  async updateClaimVerificationStatus(
    claimId: string,
    status: 'not_verified',
    disputedAt: string,
  ): Promise<ClaimRecord> {
    // Supabase: supabase.from('claims')
    //   .update({
    //     status,
    //     disputedAt,
    //     updatedAt: new Date().toISOString(),
    //   })
    //   .eq('id', claimId)
    //   .select()
    //   .single()
    throw new Error('ClaimCaseDAO.updateClaimVerificationStatus not yet wired to Supabase');
  },

  /**
   * Find a case by its claimant ID.
   */
  async getCaseByClaimantId(claimantId: string): Promise<Case | null> {
    // Supabase: supabase.from('cases')
    //   .select('*')
    //   .eq('claimantId', claimantId)
    //   .single()
    throw new Error('ClaimCaseDAO.getCaseByClaimantId not yet wired to Supabase');
  },

  /**
   * Update the drafting status of a case.
   */
  async updateCaseDraftingStatus(
    caseId: string,
    drafting_status: string,
  ): Promise<Case> {
    // Supabase: supabase.from('cases')
    //   .update({
    //     drafting_status,
    //     updatedAt: new Date().toISOString(),
    //   })
    //   .eq('id', caseId)
    //   .select()
    //   .single()
    throw new Error('ClaimCaseDAO.updateCaseDraftingStatus not yet wired to Supabase');
  },
} as const;
