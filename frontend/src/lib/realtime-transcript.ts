export interface FinalTranscriptEvent {
  dedupeKey: string;
  transcript: string;
}

interface RealtimeEvent {
  type: string;
  [key: string]: unknown;
}

const FINAL_TRANSCRIPT_EVENT_TYPE = 'conversation.item.input_audio_transcription.completed';

function hashToken(value: string): string {
  let hash = 0;
  for (let i = 0; i < value.length; i += 1) {
    hash = ((hash << 5) - hash) + value.charCodeAt(i);
    hash |= 0;
  }
  return Math.abs(hash).toString(16);
}

function readItemId(event: RealtimeEvent): string | null {
  if (typeof event.item_id === 'string' && event.item_id.trim() !== '') {
    return event.item_id;
  }

  if (
    typeof event.item === 'object'
    && event.item !== null
    && 'id' in event.item
    && typeof (event.item as { id?: unknown }).id === 'string'
  ) {
    const itemId = (event.item as { id: string }).id.trim();
    if (itemId !== '') {
      return itemId;
    }
  }

  return null;
}

function readTimestampToken(event: RealtimeEvent): string | null {
  const candidates = ['audio_end_ms', 'end_ms', 'timestamp', 'event_id'];

  for (const key of candidates) {
    const value = event[key];
    if (typeof value === 'string' && value.trim() !== '') {
      return value.trim();
    }
    if (typeof value === 'number' && Number.isFinite(value)) {
      return String(value);
    }
  }

  return null;
}

export function extractFinalTranscriptEvent(event: RealtimeEvent): FinalTranscriptEvent | null {
  if (event.type !== FINAL_TRANSCRIPT_EVENT_TYPE) {
    return null;
  }

  const transcript = typeof event.transcript === 'string' ? event.transcript.trim() : '';
  if (transcript === '') {
    return null;
  }

  const itemId = readItemId(event);
  if (itemId) {
    return {
      dedupeKey: `item:${itemId}`,
      transcript,
    };
  }

  const normalizedTranscript = transcript.toLowerCase();
  const timestampToken = readTimestampToken(event);
  const tokenBase = timestampToken
    ? `${normalizedTranscript}|${timestampToken}`
    : normalizedTranscript;

  return {
    dedupeKey: `text:${hashToken(tokenBase)}`,
    transcript,
  };
}
