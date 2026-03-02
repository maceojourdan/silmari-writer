/**
 * SessionMetricsDAO - Handles database operations for session metrics pipeline.
 *
 * Provides methods to retrieve session data with events and to persist
 * computed session metrics.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 301-store-session-metrics-on-pipeline-run
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type { AggregatedSessionDataset, SessionMetrics } from '@/server/data_structures/SessionMetrics';
import { supabase } from '@/lib/supabase';
import { MetricsPersistenceError, MetricsError, SessionNotFoundError } from '@/server/error_definitions/MetricsErrors';

function mapSessionMetrics(data: Record<string, unknown>): SessionMetrics {
  return {
    id: data.id as string | undefined,
    sessionId: (data.session_id ?? data.sessionId) as string,
    timeToFirstDraft: (data.time_to_first_draft ?? data.timeToFirstDraft) as number,
    completionRate: (data.completion_rate ?? data.completionRate) as number,
    confirmationRate: (data.confirmation_rate ?? data.confirmationRate) as number,
    signalDensity: (data.signal_density ?? data.signalDensity) as number,
    dropOff: (data.drop_off ?? data.dropOff) as number,
    createdAt: (data.created_at ?? data.createdAt) as string | undefined,
    updatedAt: (data.updated_at ?? data.updatedAt) as string | undefined,
  };
}

function mapSession(data: Record<string, unknown>) {
  return {
    id: data.id as string,
    status: data.status as 'FINALIZED',
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
    firstDraftAt: (data.first_draft_at ?? data.firstDraftAt) as string | undefined,
    finalizedAt: (data.finalized_at ?? data.finalizedAt) as string | undefined,
  };
}

function mapEvent(data: Record<string, unknown>) {
  return {
    id: data.id as string,
    sessionId: (data.session_id ?? data.sessionId) as string,
    category: data.category as 'DRAFT' | 'VERIFY' | 'FINALIZE' | 'EDIT' | 'REVISION' | 'SIGNAL',
    timestamp: data.timestamp as string,
    metadata: data.metadata as Record<string, unknown> | undefined,
  };
}

export const SessionMetricsDAO = {
  async getSessionWithEvents(sessionId: string): Promise<AggregatedSessionDataset | null> {
    try {
      const { data: sessionData, error: sessionError } = await supabase
        .from('sessions')
        .select('*')
        .eq('id', sessionId)
        .maybeSingle();

      if (sessionError) throw MetricsPersistenceError(`Failed to retrieve session: ${sessionError.message}`);
      if (!sessionData) return null;

      const { data: eventsData, error: eventsError } = await supabase
        .from('events')
        .select('*')
        .eq('session_id', sessionId);

      if (eventsError) throw MetricsPersistenceError(`Failed to retrieve events: ${eventsError.message}`);

      return {
        session: mapSession(sessionData),
        events: (eventsData as Record<string, unknown>[] || []).map(mapEvent),
      };
    } catch (err) {
      if (err instanceof MetricsError) throw err;
      throw MetricsPersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  async upsertSessionMetrics(metrics: SessionMetrics): Promise<SessionMetrics> {
    try {
      const { data, error } = await supabase
        .from('session_metrics')
        .upsert({
          session_id: metrics.sessionId,
          time_to_first_draft: metrics.timeToFirstDraft,
          completion_rate: metrics.completionRate,
          confirmation_rate: metrics.confirmationRate,
          signal_density: metrics.signalDensity,
          drop_off: metrics.dropOff,
          updated_at: new Date().toISOString(),
        })
        .select()
        .single();

      if (error) throw MetricsPersistenceError(`Failed to upsert session metrics: ${error.message}`);
      if (!data) throw MetricsPersistenceError('No data returned from session metrics upsert');
      return mapSessionMetrics(data);
    } catch (err) {
      if (err instanceof MetricsError) throw err;
      throw MetricsPersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
