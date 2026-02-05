import { describe, it, expect } from 'vitest';

describe('Voice Types and Constants', () => {
  it('should export VoiceMode enum with read_aloud and voice_edit', async () => {
    const { VOICE_MODES } = await import('@/lib/voice-types');
    expect(VOICE_MODES.READ_ALOUD).toBe('read_aloud');
    expect(VOICE_MODES.VOICE_EDIT).toBe('voice_edit');
  });

  it('should export model mapping for each voice mode', async () => {
    const { MODEL_MAP } = await import('@/lib/voice-types');
    expect(MODEL_MAP.read_aloud).toBe('gpt-4o-realtime-preview');
    expect(MODEL_MAP.voice_edit).toBe('gpt-4o-realtime-preview');
  });

  it('should export SESSION_LIMIT_MINUTES as 60', async () => {
    const { SESSION_LIMIT_MINUTES } = await import('@/lib/voice-types');
    expect(SESSION_LIMIT_MINUTES).toBe(60);
  });

  it('should export DEFAULT_VOICE as alloy', async () => {
    const { DEFAULT_VOICE } = await import('@/lib/voice-types');
    expect(DEFAULT_VOICE).toBe('alloy');
  });

  it('should export VoiceSessionState type with correct values', async () => {
    const { VOICE_SESSION_STATES } = await import('@/lib/voice-types');
    expect(VOICE_SESSION_STATES).toEqual({
      IDLE: 'idle',
      CONNECTING: 'connecting',
      CONNECTED: 'connected',
      RECONNECTING: 'reconnecting',
      ERROR: 'error',
      CLOSED: 'closed',
    });
  });

  it('should export EditEntry interface shape via factory function', async () => {
    const { createEditEntry } = await import('@/lib/voice-types');
    const entry = createEditEntry({
      messageId: 'msg-1',
      editedContent: 'new content',
      editSummary: 'Changed first paragraph',
    });
    expect(entry).toMatchObject({
      messageId: 'msg-1',
      editedContent: 'new content',
      editSummary: 'Changed first paragraph',
    });
    expect(entry.timestamp).toBeGreaterThan(0);
  });

  it('should export EditHistory interface shape via factory function', async () => {
    const { createEditHistory } = await import('@/lib/voice-types');
    const history = createEditHistory({
      projectId: 'proj-1',
      sessionId: 'session-1',
    });
    expect(history).toMatchObject({
      projectId: 'proj-1',
      sessionId: 'session-1',
      originalSnapshots: {},
      edits: [],
    });
  });
});
