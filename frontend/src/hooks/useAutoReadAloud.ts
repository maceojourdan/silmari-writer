import { useRef, useCallback, useEffect } from 'react';
import { TTSQueue } from '@/lib/tts-queue';

interface UseAutoReadAloudOptions {
  readAloudEnabled: boolean;
  isConnected: boolean;
  sendEvent: (event: Record<string, unknown>) => void;
}

export function useAutoReadAloud({ readAloudEnabled, isConnected, sendEvent }: UseAutoReadAloudOptions) {
  const queueRef = useRef<TTSQueue | null>(null);

  if (!queueRef.current) {
    queueRef.current = new TTSQueue(sendEvent);
  }

  useEffect(() => {
    queueRef.current?.setSendEvent(sendEvent);
  }, [sendEvent]);

  const onNewAssistantMessage = useCallback(
    (content: string) => {
      if (readAloudEnabled && isConnected && queueRef.current) {
        queueRef.current.enqueue(content);
      }
    },
    [readAloudEnabled, isConnected],
  );

  const handleResponseDone = useCallback(() => {
    queueRef.current?.handleResponseDone();
  }, []);

  const resetQueue = useCallback(() => {
    queueRef.current?.reset();
  }, []);

  return { onNewAssistantMessage, handleResponseDone, resetQueue };
}
