/**
 * kpiLogger - Logs primary KPI analytics recording and emission outcomes.
 *
 * Resource: cfg-p4b8 (shared_logging)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * Wraps the shared logger with path-specific context fields.
 */

import { logger } from './logger';

export const kpiLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '339-record-primary-kpi-analytics-event',
      resource: 'cfg-p4b8',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '339-record-primary-kpi-analytics-event',
      resource: 'cfg-p4b8',
      ...context,
    });
  },

  error(
    message: string,
    error?: unknown,
    context?: Record<string, unknown>,
  ): void {
    logger.error(message, error, {
      path: '339-record-primary-kpi-analytics-event',
      resource: 'cfg-p4b8',
      ...context,
    });
  },

  critical(
    message: string,
    error?: unknown,
    context?: Record<string, unknown>,
  ): void {
    logger.error(message, error, {
      path: '339-record-primary-kpi-analytics-event',
      resource: 'cfg-p4b8',
      severity: 'CRITICAL',
      ...context,
    });
  },
} as const;
