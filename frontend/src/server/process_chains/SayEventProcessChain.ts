/**
 * SayEventProcessChain - Orchestrates the SAY event voice processing
 * workflow from event interception through transcript dispatch.
 *
 * Steps:
 * 1. handleEvent(event) - Intercept and validate SAY event payload
 * 5. emitTranscriptFinal(transcript, sessionId, dispatcher) - Package and dispatch TRANSCRIPT_FINAL
 * run(event, dependencies) - Execute full pipeline
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { SayEventSchema } from '@/server/data_structures/VoiceEvent';
import type { SayEventWithSessionContext, TranscriptFinalEvent } from '@/server/data_structures/VoiceEvent';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';
import { voiceLogger } from '@/server/logging/voiceLogger';

// ---------------------------------------------------------------------------
// Process Chain
// ---------------------------------------------------------------------------

export const SayEventProcessChain = {
  /**
   * Step 1: Intercept SAY event.
   *
   * Validates the event payload using Zod schema and attaches session context.
   * Throws VoiceErrors.INVALID_SAY_PAYLOAD if payload is malformed or missing fields.
   */
  async handleEvent(event: unknown): Promise<SayEventWithSessionContext> {
    const result = SayEventSchema.safeParse(event);

    if (!result.success) {
      const error = VoiceErrors.INVALID_SAY_PAYLOAD(
        `SAY event payload validation failed: ${result.error.issues.map(i => i.message).join(', ')}`,
      );
      voiceLogger.error('INVALID_SAY_PAYLOAD', error, {
        event: typeof event === 'object' ? JSON.stringify(event) : String(event),
      });
      throw error;
    }

    const validated = result.data;

    return {
      ...validated,
      sessionContext: {
        sessionId: validated.sessionId,
        isActive: true,
      },
    };
  },

  /**
   * Step 5: Emit TRANSCRIPT_FINAL event.
   *
   * Packages transcript into TRANSCRIPT_FINAL event and dispatches via
   * the provided dispatcher function. Retries up to 2 times on failure.
   * Throws VoiceErrors.TRANSCRIPT_DISPATCH_FAILED on persistent failure.
   */
  async emitTranscriptFinal(
    transcript: string,
    sessionId: string,
    dispatcher: (event: TranscriptFinalEvent) => Promise<void>,
  ): Promise<TranscriptFinalEvent> {
    const event: TranscriptFinalEvent = {
      type: 'TRANSCRIPT_FINAL',
      text: transcript,
      sessionId,
    };

    const maxAttempts = 3;

    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
      try {
        await dispatcher(event);
        return event;
      } catch (error) {
        voiceLogger.error(
          `TRANSCRIPT_FINAL dispatch attempt ${attempt}/${maxAttempts} failed`,
          error,
          { sessionId },
        );

        if (attempt === maxAttempts) {
          throw VoiceErrors.TRANSCRIPT_DISPATCH_FAILED(
            `Failed to dispatch TRANSCRIPT_FINAL after ${maxAttempts} attempts`,
          );
        }
      }
    }

    // Unreachable, but TypeScript needs this
    throw VoiceErrors.TRANSCRIPT_DISPATCH_FAILED();
  },
} as const;
