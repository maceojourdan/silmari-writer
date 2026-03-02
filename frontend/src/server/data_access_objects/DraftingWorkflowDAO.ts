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
import { supabase } from '@/lib/supabase';
import { DomainErrors, DomainError } from '@/server/error_definitions/DomainErrors';

function mapWorkflow(data: Record<string, unknown>): DraftingWorkflow {
  return {
    id: data.id as string,
    claimId: (data.claim_id ?? data.claimId) as string,
    status: data.status as DraftingWorkflow['status'],
    reason: data.reason as string | undefined,
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
  };
}

export const DraftingWorkflowDAO = {
  async findByClaimId(claimId: string): Promise<DraftingWorkflow | null> {
    try {
      const { data, error } = await supabase
        .from('drafting_workflows')
        .select('*')
        .eq('claim_id', claimId)
        .maybeSingle();

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to find drafting workflow: ${error.message}`);
      if (!data) return null;
      return mapWorkflow(data);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatus(
    workflowId: string,
    status: DraftingWorkflowStatus,
    reason?: string,
  ): Promise<DraftingWorkflow> {
    try {
      const updatePayload: Record<string, unknown> = {
        status,
        updated_at: new Date().toISOString(),
      };
      if (reason !== undefined) {
        updatePayload.reason = reason;
      }

      const { data, error } = await supabase
        .from('drafting_workflows')
        .update(updatePayload)
        .eq('id', workflowId)
        .select()
        .single();

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to update drafting workflow status: ${error.message}`);
      if (!data) throw DomainErrors.PERSISTENCE_ERROR('No data returned from drafting workflow status update');
      return mapWorkflow(data);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
