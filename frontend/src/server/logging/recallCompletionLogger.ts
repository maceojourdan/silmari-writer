/**
 * recallCompletionLogger - Logs recall completion pipeline events including
 * slot filling, validation, state transitions, and error conditions.
 *
 * Resource: cfg-p4b8 (shared_logging)
 * Path: 319-complete-required-slots-and-end-recall-loop
 *
 * Wraps the shared logger with recall-completion-specific context fields.
 */

import { logger } from './logger';

export const recallCompletionLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '319-complete-required-slots-and-end-recall-loop',
      resource: 'cfg-p4b8',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '319-complete-required-slots-and-end-recall-loop',
      resource: 'cfg-p4b8',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '319-complete-required-slots-and-end-recall-loop',
      resource: 'cfg-p4b8',
      ...context,
    });
  },
} as const;
