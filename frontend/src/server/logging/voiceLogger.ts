/**
 * voiceLogger - Logs voice pipeline execution status and outcomes.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 *
 * Wraps the shared logger with voice-specific context fields.
 */

import { logger } from './logger';

export const voiceLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '304-backend-say-event-triggers-voice-and-transcript',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '304-backend-say-event-triggers-voice-and-transcript',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '304-backend-say-event-triggers-voice-and-transcript',
      resource: 'cfg-q9c5',
      ...context,
    });
  },
} as const;
