/**
 * verificationLogger - Logs claim verification pipeline execution.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 321-verify-key-claims-via-voice-or-sms
 *
 * Wraps the shared logger with verification-specific context fields.
 */

import { logger } from './logger';

export const verificationLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '321-verify-key-claims-via-voice-or-sms',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '321-verify-key-claims-via-voice-or-sms',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '321-verify-key-claims-via-voice-or-sms',
      ...context,
    });
  },
} as const;
