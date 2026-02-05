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

  // Use Google's public STUN servers for NAT traversal
  const pc = new RTCPeerConnection({
    iceServers: [
      { urls: 'stun:stun.l.google.com:19302' },
      { urls: 'stun:stun1.l.google.com:19302' },
    ],
  });

  // Audio output — append to DOM for autoplay to work in some browsers
  const audioEl = document.createElement('audio');
  audioEl.autoplay = true;
  audioEl.id = 'voice-session-audio';
  document.body.appendChild(audioEl);

  pc.ontrack = (event) => {
    audioEl.srcObject = event.streams[0];
  };

  // Debug: log connection state changes
  pc.oniceconnectionstatechange = () => {
    if (typeof window !== 'undefined') {
      // eslint-disable-next-line no-console
      console.log('[Voice] ICE state:', pc.iceConnectionState);
    }
  };
  pc.onconnectionstatechange = () => {
    if (typeof window !== 'undefined') {
      // eslint-disable-next-line no-console
      console.log('[Voice] Connection state:', pc.connectionState);
    }
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

  // Wait for data channel to open, then send session.update with config
  await new Promise<void>((resolve, reject) => {
    const timeout = setTimeout(() => reject(new VoiceSessionError('Data channel timeout', 'DC_TIMEOUT', true)), 10000);
    dc.onopen = () => {
      clearTimeout(timeout);
      // Send session configuration via data channel
      const sessionUpdate: Record<string, unknown> = {
        type: 'session.update',
        session: {
          voice: 'alloy',
          turn_detection: needsMicrophone ? { type: 'server_vad' } : null,
        },
      };
      if (instructions) {
        sessionUpdate.session = { ...(sessionUpdate.session as object), instructions };
      }
      if (tools && tools.length > 0) {
        sessionUpdate.session = { ...(sessionUpdate.session as object), tools };
      }
      dc.send(JSON.stringify(sessionUpdate));
      resolve();
    };
    dc.onerror = () => {
      clearTimeout(timeout);
      reject(new VoiceSessionError('Data channel error', 'DC_ERROR', true));
    };
  });

  // Session timer
  const sessionTimeout = setTimeout(() => {
    close();
  }, sessionLimitMinutes * 60 * 1000);

  function close() {
    clearTimeout(sessionTimeout);
    pc.close();
    stream?.getTracks().forEach((t) => t.stop());
    audioEl.remove();
  }

  return { pc, dc, audioEl, stream, model, sessionLimitMinutes, sessionTimeout, close };
}
