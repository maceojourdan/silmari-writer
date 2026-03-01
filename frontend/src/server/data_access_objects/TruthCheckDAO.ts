/**
 * TruthCheckDAO - Encapsulates database operations for
 * truth check entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { TruthCheck, ConfirmCommand } from '@/server/data_structures/TruthCheck';

export const TruthCheckDAO = {
  async create(data: ConfirmCommand): Promise<TruthCheck> {
    // Supabase: supabase.from('truth_checks')
    //   .insert({
    //     claim_id: data.claim_id,
    //     status: data.status,
    //     source: data.source,
    //   })
    //   .select()
    //   .single()
    throw new Error('TruthCheckDAO.create not yet wired to Supabase');
  },
} as const;
