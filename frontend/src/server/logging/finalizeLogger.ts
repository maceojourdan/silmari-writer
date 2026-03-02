/**
 * finalizeLogger - Logs finalize-without-SMS pipeline execution status and outcomes.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 336-finalize-answer-without-sms-follow-up
 *
 * Wraps the shared logger with path-specific context fields.
 */

import { logger } from './logger';

export const finalizeLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '336-finalize-answer-without-sms-follow-up',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '336-finalize-answer-without-sms-follow-up',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '336-finalize-answer-without-sms-follow-up',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  /**
   * Log a critical error that requires operational attention.
   * Used for inadvertent SMS dispatch detection (Step 4 guard clause).
   */
  critical(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '336-finalize-answer-without-sms-follow-up',
      resource: 'cfg-q9c5',
      severity: 'CRITICAL',
      ...context,
    });
  },
} as const;
