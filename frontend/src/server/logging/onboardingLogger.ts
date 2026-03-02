/**
 * onboardingLogger - Logs onboarding completion and analytics event outcomes.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * Wraps the shared logger with path-specific context fields.
 */

import { logger } from './logger';

export const onboardingLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '338-record-leading-kpi-analytics-event-on-successful-user-action',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '338-record-leading-kpi-analytics-event-on-successful-user-action',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  error(
    message: string,
    error?: unknown,
    context?: Record<string, unknown>,
  ): void {
    logger.error(message, error, {
      path: '338-record-leading-kpi-analytics-event-on-successful-user-action',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  critical(
    message: string,
    error?: unknown,
    context?: Record<string, unknown>,
  ): void {
    logger.error(message, error, {
      path: '338-record-leading-kpi-analytics-event-on-successful-user-action',
      resource: 'cfg-q9c5',
      severity: 'CRITICAL',
      ...context,
    });
  },
} as const;
