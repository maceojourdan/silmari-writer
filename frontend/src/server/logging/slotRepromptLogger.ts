/**
 * slotRepromptLogger - Logs slot re-prompt pipeline events including
 * validation, workflow guard enforcement, re-prompt generation, and errors.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 320-re-prompt-unfilled-required-slots
 *
 * Wraps the shared logger with re-prompt-specific context fields.
 */

import { logger } from './logger';

export const slotRepromptLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '320-re-prompt-unfilled-required-slots',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '320-re-prompt-unfilled-required-slots',
      resource: 'cfg-q9c5',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '320-re-prompt-unfilled-required-slots',
      resource: 'cfg-q9c5',
      ...context,
    });
  },
} as const;
