/**
 * DraftDAO - Handles database persistence for draft entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 300-finalize-approved-draft-and-log-metrics
 *
 * In production, each method performs Supabase queries against
 * the drafts table. For TDD, methods are designed to be mockable.
 */

import type { Draft, DraftStatus, FinalizeMetrics } from '@/server/data_structures/Draft';

export const DraftDAO = {
  /**
   * Find a draft by its ID.
   * Returns null if not found.
   */
  async getDraftById(id: string): Promise<Draft | null> {
    // Supabase: supabase.from('drafts').select('*').eq('id', id).single()
    throw new Error('DraftDAO.getDraftById not yet wired to Supabase');
  },

  /**
   * Update draft status and return the updated entity.
   * Throws PersistenceError on database failure.
   */
  async updateStatus(id: string, status: DraftStatus, additionalFields?: Partial<Draft>): Promise<Draft> {
    // Supabase: supabase.from('drafts').update({ status, ...additionalFields, updatedAt: new Date().toISOString() }).eq('id', id).select().single()
    throw new Error('DraftDAO.updateStatus not yet wired to Supabase');
  },

  /**
   * Insert metrics associated with a finalized draft.
   * Optional: may fail without affecting FINALIZED state.
   */
  async insertMetrics(draftId: string, metrics: FinalizeMetrics): Promise<void> {
    // Supabase: supabase.from('draft_metrics').insert({ draftId, ...metrics, createdAt: new Date().toISOString() })
    throw new Error('DraftDAO.insertMetrics not yet wired to Supabase');
  },
} as const;
