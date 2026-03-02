import { describe, expect, it } from 'vitest';
import { extractFinalTranscriptEvent } from '../realtime-transcript';

describe('extractFinalTranscriptEvent', () => {
  it('extracts completed transcript events and prefers item_id for dedupe', () => {
    const result = extractFinalTranscriptEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-123',
      transcript: '  Led migration to zero downtime.  ',
    });

    expect(result).toEqual({
      dedupeKey: 'item:item-123',
      transcript: 'Led migration to zero downtime.',
    });
  });

  it('ignores non-final transcription events', () => {
    const result = extractFinalTranscriptEvent({
      type: 'conversation.item.input_audio_transcription.delta',
      transcript: 'partial',
      item_id: 'item-123',
    });

    expect(result).toBeNull();
  });

  it('returns null for empty transcript payloads', () => {
    const result = extractFinalTranscriptEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-123',
      transcript: '   ',
    });

    expect(result).toBeNull();
  });

  it('builds a stable text-based dedupe key when item id is unavailable', () => {
    const event = {
      type: 'conversation.item.input_audio_transcription.completed',
      transcript: 'Reduced latency by 30 percent.',
      audio_end_ms: 2230,
    };

    const first = extractFinalTranscriptEvent(event);
    const second = extractFinalTranscriptEvent(event);
    const withDifferentTimestamp = extractFinalTranscriptEvent({
      ...event,
      audio_end_ms: 2250,
    });

    expect(first).not.toBeNull();
    expect(second).not.toBeNull();
    expect(withDifferentTimestamp).not.toBeNull();
    expect(first?.dedupeKey).toBe(second?.dedupeKey);
    expect(first?.dedupeKey).not.toBe(withDifferentTimestamp?.dedupeKey);
    expect(first?.dedupeKey.startsWith('text:')).toBe(true);
  });

  it('uses nested item.id when item_id is missing', () => {
    const result = extractFinalTranscriptEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      transcript: 'Improved throughput.',
      item: { id: 'nested-item-1' },
    });

    expect(result?.dedupeKey).toBe('item:nested-item-1');
  });
});
