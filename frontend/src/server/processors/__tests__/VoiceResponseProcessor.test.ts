import { describe, expect, it } from 'vitest';
import { VoiceResponseProcessor } from '../VoiceResponseProcessor';
import type { VoiceResponseProcessorResult } from '../VoiceResponseProcessor';
import type { AnswerSession } from '../../data_structures/AnswerSession';

const transcript = 'I led a cross-functional team that reduced deployment time by 40 percent.';

const baseSession: Omit<AnswerSession, 'state'> = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  userId: 'user-123',
  createdAt: '2026-02-28T00:00:00Z',
  updatedAt: '2026-02-28T00:00:00Z',
};

function makeSession(state: AnswerSession['state']): AnswerSession {
  return { ...baseSession, state };
}

describe('VoiceResponseProcessor', () => {
  it('transitions INIT -> IN_PROGRESS', () => {
    const result = VoiceResponseProcessor.process(transcript, makeSession('INIT'));

    expect(result.nextState).toBe('IN_PROGRESS');
    expect(result.updatedContent).toBe(transcript);
  });

  it('transitions IN_PROGRESS -> RECALL', () => {
    const result = VoiceResponseProcessor.process(transcript, makeSession('IN_PROGRESS'));

    expect(result.nextState).toBe('RECALL');
    expect(result.updatedContent).toBe(transcript);
  });

  it('transitions RECALL -> COMPLETE', () => {
    const result = VoiceResponseProcessor.process(transcript, makeSession('RECALL'));

    expect(result.nextState).toBe('COMPLETE');
    expect(result.updatedContent).toBe(transcript);
  });

  it('returns no-op state for unsupported transitions', () => {
    const result = VoiceResponseProcessor.process(transcript, makeSession('VERIFY'));

    expect(result.nextState).toBe('VERIFY');
    expect(result.updatedContent).toBe(transcript);
  });

  it('returns object matching VoiceResponseProcessorResult type', () => {
    const result: VoiceResponseProcessorResult = VoiceResponseProcessor.process(
      transcript,
      makeSession('INIT'),
    );

    expect(typeof result.nextState).toBe('string');
    expect(typeof result.updatedContent).toBe('string');
  });
});
