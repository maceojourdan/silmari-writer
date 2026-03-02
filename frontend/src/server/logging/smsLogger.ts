/**
 * smsLogger - Logs SMS follow-up pipeline execution status and outcomes.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * Wraps the shared logger with SMS-specific context fields.
 */

import { logger } from './logger';

export const smsLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '305-followup-sms-for-uncertain-claim',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '305-followup-sms-for-uncertain-claim',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '305-followup-sms-for-uncertain-claim',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  /**
   * Log a critical error that requires operational attention.
   * Path 335: trigger-sms-follow-up-on-answer-finalization
   */
  critical(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '335-trigger-sms-follow-up-on-answer-finalization',
      resource: 'cfg-q9c5',
      severity: 'CRITICAL',
      ...context,
    });
  },
} as const;
