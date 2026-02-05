import { describe, it, expect, vi, beforeEach } from 'vitest';

describe('TTSQueue', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should enqueue text and process immediately if idle', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('Hello world');

    expect(mockSendEvent).toHaveBeenCalledWith(
      expect.objectContaining({
        type: 'conversation.item.create',
      }),
    );
    expect(mockSendEvent).toHaveBeenCalledWith(
      expect.objectContaining({
        type: 'response.create',
      }),
    );
  });

  it('should queue multiple messages and process them in order', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('First message');
    queue.enqueue('Second message');
    queue.enqueue('Third message');

    // Only first should be sent immediately
    const createCalls = mockSendEvent.mock.calls.filter(
      ([e]: [{ type: string }]) => e.type === 'conversation.item.create',
    );
    expect(createCalls).toHaveLength(1);
    expect(createCalls[0][0].item.content[0].text).toBe('First message');
  });

  it('should process next message when current finishes', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('First');
    queue.enqueue('Second');

    // Simulate response.done event
    queue.handleResponseDone();

    const createCalls = mockSendEvent.mock.calls.filter(
      ([e]: [{ type: string }]) => e.type === 'conversation.item.create',
    );
    expect(createCalls).toHaveLength(2);
    expect(createCalls[1][0].item.content[0].text).toBe('Second');
  });

  it('should skip empty content', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('');
    queue.enqueue('   ');

    expect(mockSendEvent).not.toHaveBeenCalled();
  });

  it('should clear queue on reset', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('First');
    queue.enqueue('Second');
    queue.reset();
    queue.handleResponseDone();

    // Only the initial first message should have been sent
    const createCalls = mockSendEvent.mock.calls.filter(
      ([e]: [{ type: string }]) => e.type === 'conversation.item.create',
    );
    expect(createCalls).toHaveLength(1);
  });

  it('should report queue length', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    expect(queue.length).toBe(0);
    queue.enqueue('First');
    expect(queue.length).toBe(0); // Processing, not queued
    queue.enqueue('Second');
    expect(queue.length).toBe(1); // One waiting
  });
});
