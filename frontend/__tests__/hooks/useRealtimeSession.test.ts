import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { renderHook, act } from '@testing-library/react';

// Mock voice-session module
const mockCreateVoiceSession = vi.fn();
const mockClose = vi.fn();
vi.mock('@/lib/voice-session', () => ({
  createVoiceSession: (...args: unknown[]) => mockCreateVoiceSession(...args),
}));

// Mock fetch for token endpoint
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

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

    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        token: 'ek_test',
        model: 'gpt-4o-realtime-preview',
        sessionLimitMinutes: 60,
      }),
    });

    const mockDc = {
      onopen: null as (() => void) | null,
      onclose: null as (() => void) | null,
      onmessage: null as ((event: { data: string }) => void) | null,
      send: vi.fn(),
      readyState: 'open',
    };

    mockCreateVoiceSession.mockResolvedValue({
      pc: { close: vi.fn() },
      dc: mockDc,
      audioEl: { autoplay: true, srcObject: null },
      stream: null,
      sessionTimeout: setTimeout(() => {}, 60 * 60 * 1000),
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
    expect(result.current.timeRemaining).toBeNull();
  });

  it('should connect and transition to connected state', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockFetch).toHaveBeenCalledWith('/api/voice/session', expect.any(Object));
    expect(mockCreateVoiceSession).toHaveBeenCalledWith(
      expect.objectContaining({
        token: 'ek_test',
        model: 'gpt-4o-realtime-preview',
        needsMicrophone: false,
      }),
    );
    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('connecting');
    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('connected');
  });

  it('should request microphone for voice_edit mode', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('voice_edit');
    });

    expect(mockCreateVoiceSession).toHaveBeenCalledWith(
      expect.objectContaining({ needsMicrophone: true }),
    );
  });

  it('should disconnect and clean up resources', async () => {
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

  it('should prevent double-connect', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    // Should only have been called once
    expect(mockCreateVoiceSession).toHaveBeenCalledTimes(1);
  });

  it('should clean up on unmount', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result, unmount } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    unmount();

    expect(mockClose).toHaveBeenCalled();
  });

  it('should set error state on connection failure', async () => {
    mockFetch.mockRejectedValueOnce(new Error('Network error'));

    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('error');
  });
});
