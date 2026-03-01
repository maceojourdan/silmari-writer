/**
 * ConversationVoiceModule - Frontend module that receives TRANSCRIPT_FINAL
 * events and renders transcript messages in the conversation view.
 *
 * Resource: ui-v3n6 (module)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 *
 * Manages:
 * - Event subscription for TRANSCRIPT_FINAL events
 * - Transcript validation via TranscriptVerifier (ui-a4y1)
 * - React state updates for transcript messages
 * - Fallback error rendering on validation failure
 * - Error logging via frontendLogger (cfg-r3d7)
 */

'use client';

import { useState, useEffect, useCallback } from 'react';
import { frontendLogger } from '@/logging/index';
import { validateTranscriptPayload } from '@/verifiers/TranscriptVerifier';
import type { TranscriptPayload } from '@/verifiers/TranscriptVerifier';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface TranscriptMessage {
  text: string;
  timestamp: string;
  isError: boolean;
}

export interface ConversationVoiceModuleProps {
  sessionId: string;
  onEventHandler: (handler: (event: unknown) => void) => void;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export function ConversationVoiceModule({
  sessionId,
  onEventHandler,
}: ConversationVoiceModuleProps) {
  const [messages, setMessages] = useState<TranscriptMessage[]>([]);

  const handleEvent = useCallback(
    (event: unknown) => {
      const result = validateTranscriptPayload(event);

      if (!result.success) {
        frontendLogger.error(
          'TRANSCRIPT_VALIDATION_FAILED',
          new Error(`Transcript validation failed: ${result.errors.join(', ')}`),
          { module: 'ConversationVoiceModule', action: 'handleEvent', sessionId },
        );

        setMessages((prev) => [
          ...prev,
          {
            text: 'Unable to display transcript',
            timestamp: new Date().toISOString(),
            isError: true,
          },
        ]);
        return;
      }

      setMessages((prev) => [
        ...prev,
        {
          text: result.data.text,
          timestamp: new Date().toISOString(),
          isError: false,
        },
      ]);
    },
    [sessionId],
  );

  useEffect(() => {
    onEventHandler(handleEvent);
  }, [onEventHandler, handleEvent]);

  return (
    <div data-testid="conversation-voice-module">
      {messages.map((msg, index) => (
        <div
          key={`${msg.timestamp}-${index}`}
          data-testid={msg.isError ? 'transcript-error' : 'transcript-message'}
          className={msg.isError ? 'transcript-error' : 'transcript-message'}
        >
          {msg.text}
        </div>
      ))}
    </div>
  );
}
