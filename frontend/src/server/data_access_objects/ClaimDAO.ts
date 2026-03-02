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
import { supabase } from '@/lib/supabase';
import { DomainErrors, DomainError } from '@/server/error_definitions/DomainErrors';

function mapClaim(data: Record<string, unknown>): Claim {
  return {
    id: data.id as string,
    content: data.content as string,
    status: data.status as Claim['status'],
    smsOptIn: (data.sms_opt_in ?? data.smsOptIn) as boolean,
    phoneNumber: (data.phone_number ?? data.phoneNumber) as string | undefined,
    truth_checks: (data.truth_checks ?? []) as Claim['truth_checks'],
    created_at: data.created_at as string,
    updated_at: data.updated_at as string,
  };
}

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

function mapCaseClaim(data: Record<string, unknown>): CaseClaim {
  return {
    id: data.id as string,
    caseId: (data.case_id ?? data.caseId) as string,
    text: data.text as string,
    status: data.status as CaseClaim['status'],
    metadata: data.metadata as Record<string, unknown> | undefined,
  };
}

function mapStoryRecordClaim(data: Record<string, unknown>): StoryRecordClaim {
  return {
    id: data.id as string,
    storyRecordId: (data.story_record_id ?? data.storyRecordId) as string,
    confirmed: data.confirmed as boolean,
    content: data.content as string,
  };
}

function mapConfirmedClaim(data: Record<string, unknown>): ConfirmedClaim {
  return {
    id: data.id as string,
    sessionId: (data.session_id ?? data.sessionId) as string,
    content: data.content as string,
    status: 'CONFIRMED',
    metric: data.metric as string | undefined,
    scope: data.scope as string | undefined,
    context: data.context as string | undefined,
    created_at: data.created_at as string,
    updated_at: data.updated_at as string,
  };
}

export const ClaimDAO = {
  async findById(claimId: string): Promise<Claim | null> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('*')
        .eq('id', claimId)
        .maybeSingle();

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to find claim: ${error.message}`);
      if (!data) return null;
      return mapClaim(data);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findByPhoneNumber(phoneNumber: string): Promise<Claim | null> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('*')
        .eq('phone_number', phoneNumber)
        .eq('status', 'UNCERTAIN')
        .order('created_at', { ascending: false })
        .limit(1)
        .maybeSingle();

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to find claim by phone: ${error.message}`);
      if (!data) return null;
      return mapClaim(data);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateTruthCheck(
    claimId: string,
    verdict: TruthCheckVerdict,
    source: string,
  ): Promise<Claim> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .update({
          status: verdict === 'confirmed' ? 'CONFIRMED' : 'DENIED',
          updated_at: new Date().toISOString(),
        })
        .eq('id', claimId)
        .select()
        .single();

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to update truth check: ${error.message}`);
      if (!data) throw DomainErrors.PERSISTENCE_ERROR('No data returned from truth check update');
      return mapClaim(data);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async getUnverifiedClaimsBySession(sessionId: string): Promise<ClaimRecord[]> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('*')
        .eq('session_id', sessionId)
        .eq('status', 'unverified')
        .order('category', { ascending: true });

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to get unverified claims: ${error.message}`);
      return (data ?? []).map(mapClaimRecord);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatusToVerified(claimIds: string[]): Promise<ClaimRecord[]> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .update({
          status: 'verified',
          verified_at: new Date().toISOString(),
          updated_at: new Date().toISOString(),
        })
        .in('id', claimIds)
        .select();

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to update status to verified: ${error.message}`);
      return (data ?? []).map(mapClaimRecord);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatus(claimId: string, status: ClaimStatus): Promise<Claim> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .update({ status, updated_at: new Date().toISOString() })
        .eq('id', claimId)
        .select()
        .single();

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to update claim status: ${error.message}`);
      if (!data) throw DomainErrors.PERSISTENCE_ERROR('No data returned from claim status update');
      return mapClaim(data);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async getClaimsByCaseId(caseId: string): Promise<CaseClaim[]> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('id, case_id, text, status, metadata')
        .eq('case_id', caseId);

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to get claims by case: ${error.message}`);
      return (data ?? []).map(mapCaseClaim);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async getClaimsByStoryRecordId(storyRecordId: string): Promise<StoryRecordClaim[]> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('id, story_record_id, confirmed, content')
        .eq('story_record_id', storyRecordId);

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to get claims by story record: ${error.message}`);
      return (data ?? []).map(mapStoryRecordClaim);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async getConfirmedClaims(sessionId: string): Promise<ConfirmedClaim[]> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('id, session_id, content, status, metric, scope, context, created_at, updated_at')
        .eq('session_id', sessionId)
        .eq('status', 'CONFIRMED');

      if (error) throw DomainErrors.PERSISTENCE_ERROR(`Failed to get confirmed claims: ${error.message}`);
      return (data ?? []).map(mapConfirmedClaim);
    } catch (err) {
      if (err instanceof DomainError) throw err;
      throw DomainErrors.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
