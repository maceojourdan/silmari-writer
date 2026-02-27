'use client';

import { Mic, Square, Undo2 } from 'lucide-react';
import { useVoiceEdit } from '@/hooks/useVoiceEdit';
import { useRealtimeSession } from '@/hooks/useRealtimeSession';
import { useConversationStore } from '@/lib/store';
import VoiceSessionTimer from './VoiceSessionTimer';

export default function VoiceEditPanel() {
  const { startEditing, stopEditing, undo } = useVoiceEdit();
  const { sessionState, timeRemaining } = useRealtimeSession();
  const { editHistory } = useConversationStore();

  const isActive = sessionState === 'connected';
  const isConnecting = sessionState === 'connecting';
  const hasEdits = (editHistory?.edits.length ?? 0) > 0;

  if (!isActive && !isConnecting) {
    return (
      <button
        onClick={() => {
          void startEditing();
        }}
        aria-label="Voice Edit"
        className="flex items-center gap-1.5 px-3 py-1.5 rounded-md text-sm bg-muted text-muted-foreground hover:bg-muted/80"
      >
        <Mic className="h-4 w-4" />
        Voice Edit
      </button>
    );
  }

  return (
    <div className="flex items-center gap-2">
      <VoiceSessionTimer timeRemaining={timeRemaining} />

      <button
        onClick={undo}
        disabled={!hasEdits}
        aria-label="Undo"
        className="flex items-center gap-1 px-2 py-1 rounded text-sm text-muted-foreground hover:bg-muted disabled:opacity-50 disabled:cursor-not-allowed"
      >
        <Undo2 className="h-3.5 w-3.5" />
        Undo
      </button>

      <button
        onClick={stopEditing}
        aria-label="Stop"
        className="flex items-center gap-1 px-2 py-1 rounded text-sm bg-red-100 text-red-700 hover:bg-red-200"
      >
        <Square className="h-3.5 w-3.5" />
        Stop
      </button>

      {isConnecting && (
        <span className="text-sm text-muted-foreground animate-pulse">
          Connecting...
        </span>
      )}
    </div>
  );
}
