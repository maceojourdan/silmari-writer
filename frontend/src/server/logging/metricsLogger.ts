/**
 * metricsLogger - Logs metrics pipeline execution status and outcomes.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 301-store-session-metrics-on-pipeline-run
 *
 * Wraps the shared logger with metrics-specific context fields.
 */

import { logger } from './logger';

export const metricsLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '301-store-session-metrics-on-pipeline-run',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '301-store-session-metrics-on-pipeline-run',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '301-store-session-metrics-on-pipeline-run',
      resource: 'cfg-q9c5',
      ...context,
    });
  },
} as const;
