'use client';

/**
 * VoiceInteraction - Renders and vocalizes the next workflow step prompt,
 * signaling that no further questions are needed for the previous question_type.
 *
 * Resource: ui-w8p2 (component)
 * Path: 318-complete-voice-answer-advances-workflow
 *
 * Flow:
 *   1. Receives next-step payload with prompt text
 *   2. Renders prompt text in UI
 *   3. Attempts to vocalize prompt via Web Speech API
 *   4. On audio failure → logs error + shows fallback text
 *   5. Displays recall loop status (complete/in-progress)
 */

import { useEffect, useState } from 'react';
import { voiceInteractionLogger } from '@/logging/voiceInteractionLogger';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface NextStepPayload {
  sessionId: string;
  nextState: string;
  promptText: string;
  recallLoopDisabled: boolean;
}

export interface VoiceInteractionProps {
  payload: NextStepPayload;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function VoiceInteraction({ payload }: VoiceInteractionProps) {
  const [audioFailed, setAudioFailed] = useState(false);

  useEffect(() => {
    // Attempt to vocalize the prompt
    try {
      if (typeof window !== 'undefined' && window.speechSynthesis) {
        const utterance = new SpeechSynthesisUtterance(payload.promptText);
        window.speechSynthesis.speak(utterance);

        voiceInteractionLogger.info('Audio playback initiated', {
          sessionId: payload.sessionId,
          nextState: payload.nextState,
        });
      }
    } catch (error) {
      voiceInteractionLogger.error('Audio playback failed', error, {
        sessionId: payload.sessionId,
        nextState: payload.nextState,
      });
      setAudioFailed(true);
    }
  }, [payload.promptText, payload.sessionId, payload.nextState]);

  return (
    <div data-testid="voice-interaction" className="flex flex-col gap-4 p-4">
      {/* Next State Indicator */}
      <div
        data-testid="next-state-indicator"
        className="inline-flex items-center gap-2 text-sm font-medium text-primary"
      >
        <span className="inline-block w-2 h-2 rounded-full bg-green-500" />
        Next step: {payload.nextState}
      </div>

      {/* Prompt Text */}
      <div
        data-testid="prompt-text"
        className="text-base leading-relaxed"
      >
        {payload.promptText}
      </div>

      {/* Recall Loop Status */}
      <div
        data-testid="recall-loop-status"
        className="text-xs text-muted-foreground"
      >
        {payload.recallLoopDisabled
          ? 'Previous question complete — moving to next step'
          : 'Recall loop still active'}
      </div>

      {/* Fallback Text (shown on audio failure) */}
      {audioFailed && (
        <div
          data-testid="fallback-text"
          className="p-3 rounded-md bg-amber-50 border border-amber-200 text-sm text-amber-800"
          role="alert"
        >
          <span className="font-medium">Audio unavailable:</span>{' '}
          {payload.promptText}
        </div>
      )}
    </div>
  );
}
