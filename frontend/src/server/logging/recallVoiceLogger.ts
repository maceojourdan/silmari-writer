/**
 * recallVoiceLogger - Logs recall voice pipeline execution, slot filling,
 * and follow-up prompt delivery events.
 *
 * Resource: cfg-p4b8 (shared_logging)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 *
 * Wraps the shared logger with recall-voice-specific context fields.
 */

import { logger } from './logger';

export const recallVoiceLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '317-prompt-for-missing-slots-after-partial-voice-answer',
      resource: 'cfg-p4b8',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '317-prompt-for-missing-slots-after-partial-voice-answer',
      resource: 'cfg-p4b8',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '317-prompt-for-missing-slots-after-partial-voice-answer',
      resource: 'cfg-p4b8',
      ...context,
    });
  },
} as const;
