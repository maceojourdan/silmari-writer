import { NextRequest, NextResponse } from 'next/server';
import { MODEL_MAP, SESSION_LIMIT_MINUTES, DEFAULT_VOICE } from '@/lib/voice-types';
import type { VoiceMode } from '@/lib/voice-types';

export async function POST(request: NextRequest) {
  const apiKey = process.env.OPENAI_API_KEY;
  if (!apiKey) {
    return NextResponse.json(
      { error: 'Voice chat not configured' },
      { status: 500 },
    );
  }

  const body = await request.json();
  const mode: VoiceMode = body.mode in MODEL_MAP ? body.mode : 'read_aloud';
  const model = MODEL_MAP[mode];

  const sessionConfig: Record<string, unknown> = {
    type: 'realtime',
    model,
    audio: { output: { voice: DEFAULT_VOICE } },
  };

  if (body.instructions) {
    sessionConfig.instructions = body.instructions;
  }
  if (body.tools) {
    sessionConfig.tools = body.tools;
  }

  // GA endpoint — wraps config in { session: ... }
  const response = await fetch('https://api.openai.com/v1/realtime/client_secrets', {
    method: 'POST',
    headers: {
      'Authorization': `Bearer ${apiKey}`,
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({ session: sessionConfig }),
  });

  if (!response.ok) {
    const errBody = await response.json().catch(() => ({}));
    console.error('[Voice Session] OpenAI error:', response.status, errBody);
    return NextResponse.json(
      { error: 'Failed to create voice session', detail: errBody },
      { status: 502 },
    );
  }

  // GA response: { client_secret: "ek_...", expires_at: <unix_ts>, session: {...} }
  const data = await response.json();
  return NextResponse.json({
    token: data.client_secret,
    model,
    sessionLimitMinutes: SESSION_LIMIT_MINUTES,
  });
}
