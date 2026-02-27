import { useRef, useEffect, useCallback, useState } from 'react';
import { createVoiceSession } from '@/lib/voice-session';
import { useConversationStore } from '@/lib/store';
import type { VoiceMode } from '@/lib/voice-types';
import { VOICE_MODES } from '@/lib/voice-types';
import type { VoiceSession, VoiceEventCallback } from '@/lib/voice-session';

export function useRealtimeSession() {
  const sessionRef = useRef<VoiceSession | null>(null);
  const connectingRef = useRef(false);
  const [timeRemaining, setTimeRemaining] = useState<number | null>(null);
  const timerRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const onEventRef = useRef<VoiceEventCallback | null>(null);

  const { voiceSessionState, setVoiceSessionState } = useConversationStore();

  const setOnEvent = useCallback((callback: VoiceEventCallback | null) => {
    onEventRef.current = callback;
  }, []);

  const disconnect = useCallback(() => {
    if (timerRef.current) {
      clearInterval(timerRef.current);
      timerRef.current = null;
    }
    sessionRef.current?.close();
    sessionRef.current = null;
    setTimeRemaining(null);
    setVoiceSessionState('idle');
  }, [setVoiceSessionState]);

  const connect = useCallback(async (mode: VoiceMode, options?: {
    instructions?: string;
    tools?: unknown[];
  }) => {
    // Prevent double-connect
    if (sessionRef.current || connectingRef.current) return;
    connectingRef.current = true;

    setVoiceSessionState('connecting');

    try {
      const session = await createVoiceSession({
        mode,
        needsMicrophone: mode === VOICE_MODES.VOICE_EDIT,
        instructions: options?.instructions,
        tools: options?.tools,
        onEvent: (event) => {
          // Forward events to the registered callback
          onEventRef.current?.(event);
        },
      });

      sessionRef.current = session;
      setVoiceSessionState('connected');

      // Start countdown timer
      const endTime = Date.now() + session.sessionLimitMinutes * 60 * 1000;
      timerRef.current = setInterval(() => {
        const remaining = Math.max(0, Math.floor((endTime - Date.now()) / 1000));
        setTimeRemaining(remaining);
        if (remaining <= 0) {
          disconnect();
        }
      }, 1000);
    } catch {
      setVoiceSessionState('error');
    } finally {
      connectingRef.current = false;
    }
  }, [setVoiceSessionState, disconnect]);

  const sendEvent = useCallback((event: Record<string, unknown>) => {
    const dc = sessionRef.current?.dc;
    if (dc && dc.readyState === 'open') {
      // eslint-disable-next-line no-console
      console.log('[Voice] Sending event:', event.type, event);
      dc.send(JSON.stringify(event));
    } else {
      // eslint-disable-next-line no-console
      console.warn('[Voice] Cannot send event, dc not open:', dc?.readyState, event.type);
    }
  }, []);

  // Cleanup on unmount
  useEffect(() => {
    return () => {
      disconnect();
    };
  }, [disconnect]);

  return {
    sessionState: voiceSessionState,
    timeRemaining,
    connect,
    disconnect,
    sendEvent,
    setOnEvent,
    dataChannel: sessionRef.current?.dc ?? null,
  };
}
