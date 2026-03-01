/**
 * SpeechRequestTransformer - Transforms a validated SAY command into a
 * structured speech synthesis request payload.
 *
 * Maps to the voice subsystem's expected request format (OpenAI Realtime API).
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import type { ValidatedSayCommand, SpeechSynthesisRequest } from '@/server/data_structures/VoiceEvent';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';
import { voiceLogger } from '@/server/logging/voiceLogger';

// ---------------------------------------------------------------------------
// Default Voice Configuration
// ---------------------------------------------------------------------------

const DEFAULT_VOICE_ID = 'alloy';

// ---------------------------------------------------------------------------
// Transformer
// ---------------------------------------------------------------------------

export const SpeechRequestTransformer = {
  /**
   * Step 3: Transform validated command to speech synthesis request.
   *
   * Validates that text content is non-empty after trimming, then maps
   * the command into a structured SpeechSynthesisRequest payload.
   * Throws VoiceErrors.TRANSFORMATION_FAILED if text is invalid.
   */
  toSpeechRequest(
    command: ValidatedSayCommand,
    voiceId: string = DEFAULT_VOICE_ID,
  ): SpeechSynthesisRequest {
    const trimmedText = command.text.trim();

    if (!trimmedText) {
      const error = VoiceErrors.TRANSFORMATION_FAILED(
        `Cannot transform empty text into speech request`,
      );
      voiceLogger.error('TRANSFORMATION_FAILED', error, {
        sessionId: command.sessionId,
      });
      throw error;
    }

    return {
      text: command.text,
      voiceId,
      sessionId: command.sessionId,
    };
  },
} as const;
