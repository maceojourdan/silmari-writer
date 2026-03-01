/**
 * DraftingWorkflowDAO - Encapsulates database operations for
 * drafting workflow entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { DraftingWorkflow, DraftingWorkflowStatus } from '@/server/data_structures/DraftingWorkflow';

export const DraftingWorkflowDAO = {
  /**
   * Find a drafting workflow by claim ID.
   */
  async findByClaimId(claimId: string): Promise<DraftingWorkflow | null> {
    // Supabase: supabase.from('drafting_workflows')
    //   .select('*')
    //   .eq('claimId', claimId)
    //   .single()
    throw new Error('DraftingWorkflowDAO.findByClaimId not yet wired to Supabase');
  },

  /**
   * Update a drafting workflow's status and optional reason.
   *
   * @returns Updated drafting workflow entity.
   */
  async updateStatus(
    workflowId: string,
    status: DraftingWorkflowStatus,
    reason?: string,
  ): Promise<DraftingWorkflow> {
    // Supabase: supabase.from('drafting_workflows')
    //   .update({ status, reason, updatedAt: new Date().toISOString() })
    //   .eq('id', workflowId)
    //   .select()
    //   .single()
    throw new Error('DraftingWorkflowDAO.updateStatus not yet wired to Supabase');
  },
} as const;
