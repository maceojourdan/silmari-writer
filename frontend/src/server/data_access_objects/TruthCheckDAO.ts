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
import { supabase } from '@/lib/supabase';
import { TruthCheckErrors, TruthCheckError } from '@/server/error_definitions/TruthCheckErrors';

export const TruthCheckDAO = {
  async create(data: ConfirmCommand): Promise<TruthCheck> {
    try {
      const { data: row, error } = await supabase
        .from('truth_checks')
        .insert({
          claim_id: data.claim_id,
          status: data.status,
          source: data.source,
        })
        .select()
        .single();

      if (error) throw TruthCheckErrors.PERSISTENCE_ERROR(`Failed to create truth check: ${error.message}`);
      if (!row) throw TruthCheckErrors.PERSISTENCE_ERROR('No data returned');

      return {
        id: row.id,
        claim_id: row.claim_id,
        status: row.status,
        source: row.source,
        created_at: row.created_at,
      };
    } catch (err) {
      if (err instanceof TruthCheckError) throw err;
      throw TruthCheckErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
