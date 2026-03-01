/**
 * VoiceSynthesisService - Invokes voice synthesis, streams audio,
 * and captures the transcript text.
 *
 * Retries up to 2 times (3 total attempts) on failure before throwing.
 *
 * Resource: (service)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import type { SpeechSynthesisRequest } from '@/server/data_structures/VoiceEvent';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';
import { voiceLogger } from '@/server/logging/voiceLogger';

// ---------------------------------------------------------------------------
// Voice Client Interface (mockable)
// ---------------------------------------------------------------------------

export interface VoiceClient {
  synthesize(request: SpeechSynthesisRequest): Promise<{ transcript: string }>;
}

// ---------------------------------------------------------------------------
// Default voice client stub (not yet wired to OpenAI Realtime API)
// ---------------------------------------------------------------------------

const defaultVoiceClient: VoiceClient = {
  async synthesize(_request: SpeechSynthesisRequest): Promise<{ transcript: string }> {
    throw new Error('VoiceClient.synthesize not yet wired to OpenAI Realtime API');
  },
};

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const VoiceSynthesisService = {
  /**
   * Step 4: Synthesize and stream audio.
   *
   * Invokes the voice client to synthesize speech from the request payload.
   * Retries up to 2 times on failure (3 total attempts).
   * Returns the captured transcript text on success.
   * Throws VoiceErrors.SYNTHESIS_FAILED after all retry attempts exhausted.
   */
  async synthesizeAndStream(
    request: SpeechSynthesisRequest,
    client: VoiceClient = defaultVoiceClient,
  ): Promise<string> {
    const maxAttempts = 3;

    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
      try {
        const result = await client.synthesize(request);
        return result.transcript;
      } catch (error) {
        voiceLogger.error(
          `Voice synthesis attempt ${attempt}/${maxAttempts} failed`,
          error,
          { sessionId: request.sessionId },
        );

        if (attempt === maxAttempts) {
          throw VoiceErrors.SYNTHESIS_FAILED(
            `Speech synthesis failed after ${maxAttempts} attempts`,
          );
        }
      }
    }

    // Unreachable, but TypeScript needs this
    throw VoiceErrors.SYNTHESIS_FAILED();
  },
} as const;
