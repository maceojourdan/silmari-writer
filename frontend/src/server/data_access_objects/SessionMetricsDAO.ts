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

export const SessionMetricsDAO = {
  /**
   * Retrieve a session with its associated events by session ID.
   * Returns null if the session is not found.
   */
  async getSessionWithEvents(sessionId: string): Promise<AggregatedSessionDataset | null> {
    // Supabase: query sessions table + events table by session_id
    throw new Error('SessionMetricsDAO.getSessionWithEvents not yet wired to Supabase');
  },

  /**
   * Upsert session metrics record.
   * Creates a new record or updates existing one for the given session.
   * Returns the persisted metrics record.
   */
  async upsertSessionMetrics(metrics: SessionMetrics): Promise<SessionMetrics> {
    // Supabase: supabase.from('session_metrics').upsert(metrics).select().single()
    throw new Error('SessionMetricsDAO.upsertSessionMetrics not yet wired to Supabase');
  },
} as const;
