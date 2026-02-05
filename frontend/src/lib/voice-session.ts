export class VoiceSessionError extends Error {
  code: string;
  retryable: boolean;

  constructor(message: string, code: string, retryable = false) {
    super(message);
    this.name = 'VoiceSessionError';
    this.code = code;
    this.retryable = retryable;
  }
}

export interface VoiceSessionOptions {
  mode: string;
  needsMicrophone: boolean;
  instructions?: string;
  tools?: unknown[];
}

export interface VoiceSession {
  pc: RTCPeerConnection;
  dc: RTCDataChannel;
  audioEl: HTMLAudioElement;
  stream: MediaStream | null;
  model: string;
  sessionLimitMinutes: number;
  sessionTimeout: ReturnType<typeof setTimeout>;
  close: () => void;
}

export async function createVoiceSession(options: VoiceSessionOptions): Promise<VoiceSession> {
  const { mode, needsMicrophone, instructions, tools } = options;
  const pc = new RTCPeerConnection();

  // Audio output
  const audioEl = document.createElement('audio');
  audioEl.autoplay = true;
  pc.ontrack = (event) => {
    audioEl.srcObject = event.streams[0];
  };

  // Audio input: microphone for voice_edit, receive-only for read_aloud
  let stream: MediaStream | null = null;
  if (needsMicrophone) {
    try {
      stream = await navigator.mediaDevices.getUserMedia({ audio: true });
      pc.addTrack(stream.getAudioTracks()[0], stream);
    } catch (err) {
      pc.close();
      throw new VoiceSessionError(
        `Microphone access denied: ${(err as Error).message}`,
        'MICROPHONE_DENIED',
        false,
      );
    }
  } else {
    // Add receive-only audio transceiver so the SDP offer includes audio
    pc.addTransceiver('audio', { direction: 'recvonly' });
  }

  // Data channel for API events
  const dc = pc.createDataChannel('oai-events');

  // Create SDP offer
  const offer = await pc.createOffer();
  await pc.setLocalDescription(offer);

  // Send SDP to our server, which proxies to OpenAI with the API key
  const response = await fetch('/api/voice/session', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      sdp: pc.localDescription!.sdp!,
      mode,
      instructions,
      tools,
    }),
  });

  if (!response.ok) {
    pc.close();
    stream?.getTracks().forEach((t) => t.stop());
    const detail = await response.json().catch(() => ({}));
    throw new VoiceSessionError(
      detail.error || 'SDP exchange failed',
      'SDP_EXCHANGE_FAILED',
      true,
    );
  }

  const { sdp: answerSdp, model, sessionLimitMinutes } = await response.json();
  await pc.setRemoteDescription({ type: 'answer', sdp: answerSdp });

  // Session timer
  const sessionTimeout = setTimeout(() => {
    close();
  }, sessionLimitMinutes * 60 * 1000);

  function close() {
    clearTimeout(sessionTimeout);
    pc.close();
    stream?.getTracks().forEach((t) => t.stop());
  }

  return { pc, dc, audioEl, stream, model, sessionLimitMinutes, sessionTimeout, close };
}
