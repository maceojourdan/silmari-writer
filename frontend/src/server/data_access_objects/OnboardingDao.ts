/**
 * OnboardingDao - Handles database persistence for onboarding entities
 * and analytics events.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * In production, each method performs Supabase queries. For TDD, methods are designed to be mockable.
 */

import type { Onboarding } from '@/server/data_structures/Onboarding';
import type {
  AnalyticsEvent,
  AnalyticsEventInsert,
} from '@/server/data_structures/AnalyticsEvent';
import { supabase } from '@/lib/supabase';
import { BackendErrors, BackendError } from '@/server/error_definitions/BackendErrors';

function mapOnboarding(data: Record<string, unknown>): Onboarding {
  return {
    id: data.id as string,
    userId: (data.user_id ?? data.userId) as string,
    step: data.step as number,
    status: data.status as Onboarding['status'],
    completedAt: (data.completed_at ?? data.completedAt) as string | null,
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
  };
}

function mapAnalyticsEvent(data: Record<string, unknown>): AnalyticsEvent {
  return {
    id: data.id as string,
    kpiId: (data.kpi_id ?? data.kpiId) as string,
    userId: (data.user_id ?? data.userId) as string,
    timestamp: data.timestamp as string,
    metadata: data.metadata as Record<string, unknown>,
    createdAt: (data.created_at ?? data.createdAt) as string,
  };
}

export const OnboardingDao = {
  async findByUserAndStep(
    userId: string,
    step: number,
  ): Promise<Onboarding | null> {
    try {
      const { data, error } = await supabase
        .from('onboarding')
        .select('*')
        .eq('user_id', userId)
        .eq('step', step)
        .maybeSingle();

      if (error) throw BackendErrors.PersistenceFailed(`Failed to find onboarding: ${error.message}`);
      if (!data) return null;
      return mapOnboarding(data);
    } catch (err) {
      if (err instanceof BackendError) throw err;
      throw BackendErrors.PersistenceFailed(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateOnboardingStep(
    userId: string,
    step: number,
    fields: Partial<Pick<Onboarding, 'status' | 'completedAt' | 'updatedAt'>>,
  ): Promise<Onboarding> {
    try {
      const updatePayload: Record<string, unknown> = {
        updated_at: new Date().toISOString(),
      };
      if (fields.status !== undefined) updatePayload.status = fields.status;
      if (fields.completedAt !== undefined) updatePayload.completed_at = fields.completedAt;

      const { data, error } = await supabase
        .from('onboarding')
        .update(updatePayload)
        .eq('user_id', userId)
        .eq('step', step)
        .select()
        .single();

      if (error) throw BackendErrors.PersistenceFailed(`Failed to update onboarding step: ${error.message}`);
      if (!data) throw BackendErrors.PersistenceFailed('No data returned from onboarding step update');
      return mapOnboarding(data);
    } catch (err) {
      if (err instanceof BackendError) throw err;
      throw BackendErrors.PersistenceFailed(`Unexpected: ${(err as Error).message}`);
    }
  },

  async createOnboarding(
    data: Pick<Onboarding, 'userId' | 'step'>,
  ): Promise<Onboarding> {
    try {
      const { data: row, error } = await supabase
        .from('onboarding')
        .insert([{
          user_id: data.userId,
          step: data.step,
          status: 'NOT_STARTED',
        }])
        .select()
        .single();

      if (error) throw BackendErrors.PersistenceFailed(`Failed to create onboarding: ${error.message}`);
      if (!row) throw BackendErrors.PersistenceFailed('No data returned from onboarding creation');
      return mapOnboarding(row);
    } catch (err) {
      if (err instanceof BackendError) throw err;
      throw BackendErrors.PersistenceFailed(`Unexpected: ${(err as Error).message}`);
    }
  },

  async insertAnalyticsEvent(
    data: AnalyticsEventInsert,
  ): Promise<AnalyticsEvent> {
    try {
      const { data: row, error } = await supabase
        .from('analytics_events')
        .insert([{
          kpi_id: data.kpiId,
          user_id: data.userId,
          timestamp: data.timestamp,
          metadata: data.metadata,
        }])
        .select()
        .single();

      if (error) throw BackendErrors.AnalyticsPersistenceFailed(`Failed to insert analytics event: ${error.message}`);
      if (!row) throw BackendErrors.AnalyticsPersistenceFailed('No data returned from analytics event insert');
      return mapAnalyticsEvent(row);
    } catch (err) {
      if (err instanceof BackendError) throw err;
      throw BackendErrors.AnalyticsPersistenceFailed(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findAnalyticsEvent(
    userId: string,
    kpiId: string,
    metadata: Record<string, unknown>,
  ): Promise<AnalyticsEvent | null> {
    try {
      const { data, error } = await supabase
        .from('analytics_events')
        .select('*')
        .eq('user_id', userId)
        .eq('kpi_id', kpiId)
        .maybeSingle();

      if (error) throw BackendErrors.AnalyticsPersistenceFailed(`Failed to find analytics event: ${error.message}`);
      if (!data) return null;
      return mapAnalyticsEvent(data);
    } catch (err) {
      if (err instanceof BackendError) throw err;
      throw BackendErrors.AnalyticsPersistenceFailed(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
