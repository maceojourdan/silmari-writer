/**
 * voiceInteractionLogger - Frontend logger for the VoiceInteraction
 * component, capturing audio playback and UI rendering events.
 *
 * Resource: cfg-r3d7 (frontend_logging)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import { frontendLogger } from './index';

export const voiceInteractionLogger = {
  info(message: string, context?: Record<string, unknown>): void {
    frontendLogger.info(message, {
      component: 'VoiceInteraction',
      path: '318-complete-voice-answer-advances-workflow',
      ...context,
    });
  },

  warn(message: string, context?: Record<string, unknown>): void {
    frontendLogger.warn(message, {
      component: 'VoiceInteraction',
      path: '318-complete-voice-answer-advances-workflow',
      ...context,
    });
  },

  error(message: string, error?: unknown, context?: Record<string, unknown>): void {
    frontendLogger.error(message, error, {
      component: 'VoiceInteraction',
      path: '318-complete-voice-answer-advances-workflow',
      ...context,
    });
  },
} as const;
