import { describe, it, expect, vi, beforeEach } from 'vitest';
import { renderHook } from '@testing-library/react';

const mockEnqueue = vi.fn();
interface MockQueueInstance {
  enqueue: typeof mockEnqueue;
  handleResponseDone: ReturnType<typeof vi.fn>;
  reset: ReturnType<typeof vi.fn>;
  setSendEvent: ReturnType<typeof vi.fn>;
  length: number;
}

vi.mock('@/lib/tts-queue', () => ({
  TTSQueue: vi.fn().mockImplementation(function (this: MockQueueInstance) {
    this.enqueue = mockEnqueue;
    this.handleResponseDone = vi.fn();
    this.reset = vi.fn();
    this.setSendEvent = vi.fn();
    this.length = 0;
  }),
}));

describe('useAutoReadAloud', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should enqueue new assistant messages when readAloudEnabled is true', async () => {
    const { useAutoReadAloud } = await import('@/hooks/useAutoReadAloud');
    const { result } = renderHook(() =>
      useAutoReadAloud({
        readAloudEnabled: true,
        isConnected: true,
        sendEvent: vi.fn(),
      }),
    );

    result.current.onNewAssistantMessage('Hello from the agent');

    expect(mockEnqueue).toHaveBeenCalledWith('Hello from the agent');
  });

  it('should NOT enqueue when readAloudEnabled is false', async () => {
    const { useAutoReadAloud } = await import('@/hooks/useAutoReadAloud');
    const { result } = renderHook(() =>
      useAutoReadAloud({
        readAloudEnabled: false,
        isConnected: true,
        sendEvent: vi.fn(),
      }),
    );

    result.current.onNewAssistantMessage('Hello');

    expect(mockEnqueue).not.toHaveBeenCalled();
  });

  it('should NOT enqueue when session is not connected', async () => {
    const { useAutoReadAloud } = await import('@/hooks/useAutoReadAloud');
    const { result } = renderHook(() =>
      useAutoReadAloud({
        readAloudEnabled: true,
        isConnected: false,
        sendEvent: vi.fn(),
      }),
    );

    result.current.onNewAssistantMessage('Hello');

    expect(mockEnqueue).not.toHaveBeenCalled();
  });
});
