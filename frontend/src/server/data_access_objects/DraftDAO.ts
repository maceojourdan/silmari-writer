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
import { supabase } from '@/lib/supabase';
import { DraftDataAccessError, DraftError } from '@/server/error_definitions/DraftErrors';

function mapDraft(data: Record<string, unknown>): Draft {
  return {
    id: data.id as string,
    status: data.status as Draft['status'],
    content: data.content as string,
    title: data.title as string | undefined,
    userId: (data.user_id ?? data.userId) as string,
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
    approvedAt: (data.approved_at ?? data.approvedAt) as string | undefined,
    finalizedAt: (data.finalized_at ?? data.finalizedAt) as string | undefined,
  };
}

export const DraftDAO = {
  async getDraftById(id: string): Promise<Draft | null> {
    try {
      const { data, error } = await supabase
        .from('drafts')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw DraftDataAccessError.RETRIEVAL_FAILED(`Failed to get draft: ${error.message}`);
      if (!data) return null;
      return mapDraft(data);
    } catch (err) {
      if (err instanceof DraftError) throw err;
      throw DraftDataAccessError.RETRIEVAL_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatus(id: string, status: DraftStatus, additionalFields?: Partial<Draft>): Promise<Draft> {
    try {
      const updatePayload: Record<string, unknown> = {
        status,
        updated_at: new Date().toISOString(),
      };
      if (additionalFields) {
        Object.assign(updatePayload, additionalFields);
      }

      const { data, error } = await supabase
        .from('drafts')
        .update(updatePayload)
        .eq('id', id)
        .select()
        .single();

      if (error) throw DraftDataAccessError.PERSISTENCE_FAILED(`Failed to update draft status: ${error.message}`);
      if (!data) throw DraftDataAccessError.PERSISTENCE_FAILED('No data returned from draft status update');
      return mapDraft(data);
    } catch (err) {
      if (err instanceof DraftError) throw err;
      throw DraftDataAccessError.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async insertMetrics(draftId: string, metrics: FinalizeMetrics): Promise<void> {
    try {
      const { error } = await supabase
        .from('draft_metrics')
        .insert({
          draft_id: draftId,
          time_to_draft: metrics.timeToDraft,
          confirmation_rate: metrics.confirmationRate,
          signal_density: metrics.signalDensity,
          created_at: new Date().toISOString(),
        });

      if (error) throw DraftDataAccessError.PERSISTENCE_FAILED(`Failed to insert draft metrics: ${error.message}`);
    } catch (err) {
      if (err instanceof DraftError) throw err;
      throw DraftDataAccessError.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
