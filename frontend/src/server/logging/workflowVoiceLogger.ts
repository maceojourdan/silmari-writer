/**
 * workflowVoiceLogger - Logs workflow voice pipeline execution,
 * slot completion, and workflow advancement events.
 *
 * Resource: cfg-r3d7 (frontend_logging)
 * Path: 318-complete-voice-answer-advances-workflow
 *
 * Wraps the shared logger with workflow-voice-specific context fields.
 */

import { logger } from './logger';

export const workflowVoiceLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    logger.info(message, {
      path: '318-complete-voice-answer-advances-workflow',
      resource: 'cfg-r3d7',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    logger.warn(message, {
      path: '318-complete-voice-answer-advances-workflow',
      resource: 'cfg-r3d7',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    logger.error(message, error, {
      path: '318-complete-voice-answer-advances-workflow',
      resource: 'cfg-r3d7',
      ...context,
    });
  },
} as const;
