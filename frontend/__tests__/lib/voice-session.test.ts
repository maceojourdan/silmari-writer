import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

// Mock RTCPeerConnection
const mockAddTrack = vi.fn();
const mockAddTransceiver = vi.fn();
const mockCreateDataChannel = vi.fn();
const mockCreateOffer = vi.fn();
const mockSetLocalDescription = vi.fn();
const mockSetRemoteDescription = vi.fn();
const mockClose = vi.fn();
let mockOnTrack: ((event: { streams: MediaStream[] }) => void) | null = null;

// eslint-disable-next-line @typescript-eslint/no-explicit-any
const MockRTCPeerConnection = vi.fn().mockImplementation(function (this: any) {
  this.addTrack = mockAddTrack;
  this.addTransceiver = mockAddTransceiver;
  this.createDataChannel = mockCreateDataChannel.mockReturnValue({
    onopen: null,
    onclose: null,
    onmessage: null,
    send: vi.fn(),
    readyState: 'open',
  });
  this.createOffer = mockCreateOffer.mockResolvedValue({ sdp: 'mock-offer-sdp' });
  this.setLocalDescription = mockSetLocalDescription.mockResolvedValue(undefined);
  this.setRemoteDescription = mockSetRemoteDescription.mockResolvedValue(undefined);
  this.close = mockClose;
  this.localDescription = { sdp: 'mock-offer-sdp' };
  Object.defineProperty(this, 'ontrack', {
    get() { return mockOnTrack; },
    set(handler: (event: { streams: MediaStream[] }) => void) { mockOnTrack = handler; },
    configurable: true,
  });
});

vi.stubGlobal('RTCPeerConnection', MockRTCPeerConnection);

// Mock fetch for SDP exchange
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// Mock navigator.mediaDevices
const mockGetUserMedia = vi.fn();
vi.stubGlobal('navigator', {
  mediaDevices: { getUserMedia: mockGetUserMedia },
});

// Mock Audio element - use a stored reference to the real createElement
const realCreateElement = document.createElement.bind(document);
const mockAudioEl = { autoplay: false, srcObject: null as MediaStream | null };
vi.spyOn(document, 'createElement').mockImplementation((tag: string) => {
  if (tag === 'audio') return mockAudioEl as unknown as HTMLElement;
  return realCreateElement(tag);
});

describe('createVoiceSession', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.useFakeTimers();
    mockOnTrack = null;
    mockAudioEl.autoplay = false;
    mockAudioEl.srcObject = null;
    mockFetch.mockResolvedValue({
      ok: true,
      text: async () => 'mock-answer-sdp',
    });
    mockGetUserMedia.mockResolvedValue({
      getAudioTracks: () => [{ stop: vi.fn(), kind: 'audio' }],
      getTracks: () => [{ stop: vi.fn() }],
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('should create RTCPeerConnection and data channel', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    const session = await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(MockRTCPeerConnection).toHaveBeenCalled();
    expect(mockCreateDataChannel).toHaveBeenCalledWith('oai-events');
    expect(session.pc).toBeDefined();
    expect(session.dc).toBeDefined();
  });

  it('should set audio element autoplay and attach to ontrack', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(mockAudioEl.autoplay).toBe(true);
    // Simulate track event
    const mockStream = {} as MediaStream;
    mockOnTrack?.({ streams: [mockStream] });
    expect(mockAudioEl.srcObject).toBe(mockStream);
  });

  it('should NOT request microphone for read_aloud (needsMicrophone: false)', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(mockGetUserMedia).not.toHaveBeenCalled();
    expect(mockAddTrack).not.toHaveBeenCalled();
    // Should add a recvonly transceiver for receiving audio
    expect(mockAddTransceiver).toHaveBeenCalledWith('audio', { direction: 'recvonly' });
  });

  it('should request microphone for voice_edit (needsMicrophone: true)', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: true,
    });

    expect(mockGetUserMedia).toHaveBeenCalledWith({ audio: true });
    expect(mockAddTrack).toHaveBeenCalled();
  });

  it('should perform SDP offer/answer exchange with OpenAI GA endpoint using FormData', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(mockCreateOffer).toHaveBeenCalled();
    expect(mockSetLocalDescription).toHaveBeenCalled();
    expect(mockFetch).toHaveBeenCalledWith(
      'https://api.openai.com/v1/realtime/calls',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          'Authorization': 'Bearer ek_test',
        }),
        body: expect.any(FormData),
      }),
    );
    expect(mockSetRemoteDescription).toHaveBeenCalledWith({
      type: 'answer',
      sdp: 'mock-answer-sdp',
    });
  });

  it('should set up session timeout that closes connection', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    const session = await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(session.sessionTimeout).toBeDefined();

    // Advance timer to 60 minutes
    vi.advanceTimersByTime(60 * 60 * 1000);

    expect(mockClose).toHaveBeenCalled();
  });

  it('should throw VoiceSessionError when getUserMedia is rejected', async () => {
    mockGetUserMedia.mockRejectedValueOnce(new DOMException('Permission denied'));

    const { createVoiceSession, VoiceSessionError } = await import('@/lib/voice-session');
    await expect(createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: true,
    })).rejects.toThrow(VoiceSessionError);
  });

  it('should throw VoiceSessionError when SDP exchange fails', async () => {
    mockFetch.mockResolvedValueOnce({ ok: false, status: 500, text: async () => 'Error' });

    const { createVoiceSession, VoiceSessionError } = await import('@/lib/voice-session');
    await expect(createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    })).rejects.toThrow(VoiceSessionError);
  });

  it('should return cleanup function that releases all resources', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    const session = await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-4o-realtime-preview',
      sessionLimitMinutes: 60,
      needsMicrophone: true,
    });

    session.close();

    expect(mockClose).toHaveBeenCalled();
  });
});
