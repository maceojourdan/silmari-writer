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
import { supabase } from '@/lib/supabase';
import { VerificationErrors, VerificationError } from '@/server/error_definitions/VerificationErrors';

function mapClaimRecord(data: Record<string, unknown>): ClaimRecord {
  return {
    id: data.id as string,
    sessionId: (data.session_id ?? data.sessionId) as string,
    category: data.category as ClaimRecord['category'],
    status: data.status as ClaimRecord['status'],
    contactPhone: (data.contact_phone ?? data.contactPhone) as string | undefined,
    contactMethod: (data.contact_method ?? data.contactMethod) as ClaimRecord['contactMethod'],
    content: data.content as string,
    verifiedAt: (data.verified_at ?? data.verifiedAt) as string | null | undefined,
    disputedAt: (data.disputed_at ?? data.disputedAt) as string | null | undefined,
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
  };
}

function mapCase(data: Record<string, unknown>): Case {
  return {
    id: data.id as string,
    claimantId: (data.claimant_id ?? data.claimantId) as string,
    sessionId: (data.session_id ?? data.sessionId) as string,
    drafting_status: data.drafting_status as Case['drafting_status'],
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
  };
}

export const ClaimCaseDAO = {
  async getClaimById(claimId: string): Promise<ClaimRecord | null> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('*')
        .eq('id', claimId)
        .maybeSingle();

      if (error) throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to get claim: ${error.message}`);
      if (!data) return null;
      return mapClaimRecord(data);
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateClaimVerificationStatus(
    claimId: string,
    status: 'not_verified',
    disputedAt: string,
  ): Promise<ClaimRecord> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .update({
          status,
          disputed_at: disputedAt,
          updated_at: new Date().toISOString(),
        })
        .eq('id', claimId)
        .select()
        .single();

      if (error) throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to update claim verification status: ${error.message}`);
      if (!data) throw VerificationErrors.DATA_ACCESS_ERROR('No data returned from claim verification status update');
      return mapClaimRecord(data);
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async getCaseByClaimantId(claimantId: string): Promise<Case | null> {
    try {
      const { data, error } = await supabase
        .from('cases')
        .select('*')
        .eq('claimant_id', claimantId)
        .maybeSingle();

      if (error) throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to get case: ${error.message}`);
      if (!data) return null;
      return mapCase(data);
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateCaseDraftingStatus(
    caseId: string,
    drafting_status: string,
  ): Promise<Case> {
    try {
      const { data, error } = await supabase
        .from('cases')
        .update({
          drafting_status,
          updated_at: new Date().toISOString(),
        })
        .eq('id', caseId)
        .select()
        .single();

      if (error) throw VerificationErrors.DATA_ACCESS_ERROR(`Failed to update case drafting status: ${error.message}`);
      if (!data) throw VerificationErrors.DATA_ACCESS_ERROR('No data returned from case drafting status update');
      return mapCase(data);
    } catch (err) {
      if (err instanceof VerificationError) throw err;
      throw VerificationErrors.DATA_ACCESS_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
