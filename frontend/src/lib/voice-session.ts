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
  token: string;
  model: string;
  sessionLimitMinutes: number;
  needsMicrophone: boolean;
}

export interface VoiceSession {
  pc: RTCPeerConnection;
  dc: RTCDataChannel;
  audioEl: HTMLAudioElement;
  stream: MediaStream | null;
  sessionTimeout: ReturnType<typeof setTimeout>;
  close: () => void;
}

export async function createVoiceSession(options: VoiceSessionOptions): Promise<VoiceSession> {
  const { token, model, sessionLimitMinutes, needsMicrophone } = options;
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

  // SDP exchange — GA endpoint uses FormData
  const offer = await pc.createOffer();
  await pc.setLocalDescription(offer);

  const formData = new FormData();
  formData.set('sdp', pc.localDescription!.sdp!);
  formData.set('session', JSON.stringify({ type: 'realtime', model }));

  const sdpResponse = await fetch('https://api.openai.com/v1/realtime/calls', {
    method: 'POST',
    headers: { 'Authorization': `Bearer ${token}` },
    body: formData,
  });

  if (!sdpResponse.ok) {
    pc.close();
    stream?.getTracks().forEach((t) => t.stop());
    throw new VoiceSessionError(
      'SDP exchange failed',
      'SDP_EXCHANGE_FAILED',
      true,
    );
  }

  const answerSdp = await sdpResponse.text();
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

  return { pc, dc, audioEl, stream, sessionTimeout, close };
}
