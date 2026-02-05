import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { renderHook, act } from '@testing-library/react';

// Mock voice-session module
const mockCreateVoiceSession = vi.fn();
const mockClose = vi.fn();
vi.mock('@/lib/voice-session', () => ({
  createVoiceSession: (...args: unknown[]) => mockCreateVoiceSession(...args),
}));

// Mock store
const mockSetVoiceSessionState = vi.fn();
vi.mock('@/lib/store', () => ({
  useConversationStore: Object.assign(
    vi.fn(() => ({
      voiceSessionState: 'idle',
      setVoiceSessionState: mockSetVoiceSessionState,
    })),
    { getState: vi.fn(() => ({ setVoiceSessionState: mockSetVoiceSessionState })) },
  ),
}));

describe('useRealtimeSession', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.useFakeTimers();

    mockCreateVoiceSession.mockResolvedValue({
      pc: {},
      dc: { readyState: 'open', send: vi.fn() },
      audioEl: {},
      stream: null,
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      sessionTimeout: setTimeout(() => {}, 0),
      close: mockClose,
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('should start in idle state', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());
    expect(result.current.sessionState).toBe('idle');
  });

  it('should call createVoiceSession with mode and options on connect', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockCreateVoiceSession).toHaveBeenCalledWith(
      expect.objectContaining({
        mode: 'read_aloud',
        needsMicrophone: false,
        instructions: undefined,
        tools: undefined,
      }),
    );
  });

  it('should set needsMicrophone true for voice_edit mode', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('voice_edit', { instructions: 'test' });
    });

    expect(mockCreateVoiceSession).toHaveBeenCalledWith(
      expect.objectContaining({
        mode: 'voice_edit',
        needsMicrophone: true,
        instructions: 'test',
        tools: undefined,
      }),
    );
  });

  it('should set state to connecting then connected on successful connect', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('connecting');
    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('connected');
  });

  it('should set state to error on failed connect', async () => {
    mockCreateVoiceSession.mockRejectedValueOnce(new Error('Failed'));

    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('error');
  });

  it('should close session on disconnect', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    act(() => {
      result.current.disconnect();
    });

    expect(mockClose).toHaveBeenCalled();
    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('idle');
  });

  it('should prevent double connect', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockCreateVoiceSession).toHaveBeenCalledTimes(1);
  });
});
