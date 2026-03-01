/**
 * StoreSessionMetricsProcessChain - Orchestrates the session metrics
 * computation workflow for completed sessions.
 *
 * Steps:
 * 1. start(sessionId) - Validate and create job context
 * 2. loadSessionData(jobContext) - Fetch session + events from DAO
 * 3. computeMetrics(dataset) - Calculate five metric values
 * 4. persistMetrics(sessionId, metrics) - Store metrics via DAO
 * 5. markSuccess(persistedMetrics) - Record pipeline success
 * run(sessionId) - Execute full pipeline
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 301-store-session-metrics-on-pipeline-run
 */

import { z } from 'zod';
import {
  InvalidSessionIdentifierError,
  SessionNotFoundError,
  SessionNotCompletedError,
  MetricsPersistenceError,
  MetricsPipelineOperationalError,
} from '@/server/error_definitions/MetricsErrors';
import { metricsLogger } from '@/server/logging/metricsLogger';
import { SessionMetricsDAO } from '@/server/data_access_objects/SessionMetricsDAO';
import { SessionMetricsVerifier } from '@/server/verifiers/SessionMetricsVerifier';
import type { AggregatedSessionDataset, SessionMetrics } from '@/server/data_structures/SessionMetrics';

// ---------------------------------------------------------------------------
// Job Context
// ---------------------------------------------------------------------------

export interface JobContext {
  sessionId: string;
}

// ---------------------------------------------------------------------------
// Computed Metrics (before persistence)
// ---------------------------------------------------------------------------

export interface ComputedMetrics {
  timeToFirstDraft: number;
  completionRate: number;
  confirmationRate: number;
  signalDensity: number;
  dropOff: number;
}

// ---------------------------------------------------------------------------
// UUID Validation Schema
// ---------------------------------------------------------------------------

const SessionIdSchema = z.string().uuid();

// ---------------------------------------------------------------------------
// Process Chain
// ---------------------------------------------------------------------------

export const StoreSessionMetricsProcessChain = {
  /**
   * Step 1: Trigger metrics process chain.
   *
   * Validates the session identifier and returns a job context.
   * Throws InvalidSessionIdentifierError if the ID is missing or malformed.
   */
  start(sessionId: string): JobContext {
    const result = SessionIdSchema.safeParse(sessionId);

    if (!result.success) {
      throw InvalidSessionIdentifierError(
        `Session identifier is missing or malformed: ${sessionId}`,
      );
    }

    return { sessionId: result.data };
  },

  /**
   * Step 2: Load session and event data.
   *
   * Fetches session core data and associated event records via DAO.
   * Validates that the session exists and is in FINALIZED state.
   * Throws SessionNotFoundError or SessionNotCompletedError on failure.
   */
  async loadSessionData(jobContext: JobContext): Promise<AggregatedSessionDataset> {
    const dataset = await SessionMetricsDAO.getSessionWithEvents(jobContext.sessionId);

    if (!dataset) {
      throw SessionNotFoundError(
        `Session '${jobContext.sessionId}' not found`,
      );
    }

    if (dataset.session.status !== 'FINALIZED') {
      throw SessionNotCompletedError(
        `Session '${jobContext.sessionId}' is in '${dataset.session.status}' state, expected 'FINALIZED'`,
      );
    }

    return dataset;
  },

  /**
   * Step 3: Compute session metrics.
   *
   * Calculates five metrics from the aggregated session dataset:
   * - timeToFirstDraft: ms from session creation to first draft
   * - completionRate: FINALIZE events / total events
   * - confirmationRate: VERIFY events / (DRAFT + VERIFY + FINALIZE) events
   * - signalDensity: SIGNAL events / (EDIT + REVISION) events
   * - dropOff: 1 - completionRate
   *
   * Validates input with SessionMetricsVerifier before computation.
   * Throws InvalidMetricsInputError if required data is missing.
   */
  computeMetrics(dataset: AggregatedSessionDataset): ComputedMetrics {
    // Validate required fields via verifier
    SessionMetricsVerifier.validate(dataset);

    const { session, events } = dataset;

    // Time-to-first-draft: ms from session creation to first draft
    const createdAt = new Date(session.createdAt).getTime();
    const firstDraftAt = new Date(session.firstDraftAt!).getTime();
    const timeToFirstDraft = firstDraftAt - createdAt;

    // Count events by category
    const totalEvents = events.length;
    const draftEvents = events.filter(e => e.category === 'DRAFT').length;
    const verifyEvents = events.filter(e => e.category === 'VERIFY').length;
    const finalizeEvents = events.filter(e => e.category === 'FINALIZE').length;
    const editEvents = events.filter(e => e.category === 'EDIT').length;
    const revisionEvents = events.filter(e => e.category === 'REVISION').length;
    const signalEvents = events.filter(e => e.category === 'SIGNAL').length;

    // Completion rate: FINALIZE events / total events
    const completionRate = totalEvents > 0 ? finalizeEvents / totalEvents : 0;

    // Confirmation rate: VERIFY events / (DRAFT + VERIFY + FINALIZE) workflow events
    const workflowEvents = draftEvents + verifyEvents + finalizeEvents;
    const confirmationRate = workflowEvents > 0 ? verifyEvents / workflowEvents : 0;

    // Signal density: SIGNAL events / (EDIT + REVISION) action events
    const actionEvents = editEvents + revisionEvents;
    const signalDensity = actionEvents > 0 ? signalEvents / actionEvents : 0;

    // Drop-off: inverse of completion rate
    const dropOff = 1 - completionRate;

    return {
      timeToFirstDraft,
      completionRate,
      confirmationRate,
      signalDensity,
      dropOff,
    };
  },

  /**
   * Step 4: Persist metrics record.
   *
   * Stores or updates the metrics record via DAO.
   * On failure, logs the error and throws MetricsPersistenceError.
   */
  async persistMetrics(
    sessionId: string,
    computed: ComputedMetrics,
  ): Promise<SessionMetrics> {
    const metricsPayload: SessionMetrics = {
      sessionId,
      ...computed,
    };

    try {
      return await SessionMetricsDAO.upsertSessionMetrics(metricsPayload);
    } catch (error) {
      metricsLogger.error(
        'Failed to persist session metrics',
        error,
        { sessionId },
      );
      throw MetricsPersistenceError(
        `Failed to persist session metrics for session '${sessionId}'`,
      );
    }
  },

  /**
   * Step 5: Mark metrics pipeline success.
   *
   * Records successful completion for observability.
   * Throws MetricsPipelineOperationalError if logging/state write fails.
   */
  markSuccess(persistedMetrics: SessionMetrics): { sessionId: string; status: 'SUCCESS' } {
    try {
      metricsLogger.info('Session metrics pipeline completed successfully', {
        sessionId: persistedMetrics.sessionId,
        timeToFirstDraft: persistedMetrics.timeToFirstDraft,
        completionRate: persistedMetrics.completionRate,
        confirmationRate: persistedMetrics.confirmationRate,
        signalDensity: persistedMetrics.signalDensity,
        dropOff: persistedMetrics.dropOff,
      });

      return {
        sessionId: persistedMetrics.sessionId,
        status: 'SUCCESS',
      };
    } catch (error) {
      throw MetricsPipelineOperationalError(
        `Failed to record pipeline success for session '${persistedMetrics.sessionId}'`,
      );
    }
  },

  /**
   * Run the full pipeline: start → loadSessionData → computeMetrics → persistMetrics → markSuccess
   */
  async run(sessionId: string): Promise<{ sessionId: string; status: 'SUCCESS' }> {
    const jobContext = this.start(sessionId);
    const dataset = await this.loadSessionData(jobContext);
    const computed = this.computeMetrics(dataset);
    const persisted = await this.persistMetrics(jobContext.sessionId, computed);
    return this.markSuccess(persisted);
  },
} as const;
