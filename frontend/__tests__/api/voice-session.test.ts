import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock fetch for OpenAI API calls
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// Mock environment
const originalEnv = process.env;

function createRequest(body: Record<string, unknown>): NextRequest {
  return new NextRequest('http://localhost:3000/api/voice/session', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

const MOCK_SDP = 'v=0\r\no=- 123 2 IN IP4 127.0.0.1\r\ns=-\r\n';
const MOCK_ANSWER_SDP = 'v=0\r\no=- 456 2 IN IP4 10.0.0.1\r\ns=-\r\n';

describe('POST /api/voice/session', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.resetModules();
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-key' };
  });

  afterEach(() => {
    process.env = originalEnv;
  });

  it('should proxy SDP exchange and return answer for read_aloud mode', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      text: async () => MOCK_ANSWER_SDP,
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud', sdp: MOCK_SDP }));
    const data = await response.json();

    expect(response.status).toBe(200);
    expect(data.sdp).toBe(MOCK_ANSWER_SDP);
    expect(data.model).toBe('gpt-4o-realtime-preview');
    expect(data.sessionLimitMinutes).toBe(60);
  });

  it('should forward SDP to OpenAI /v1/realtime/calls with API key', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      text: async () => MOCK_ANSWER_SDP,
    });

    const { POST } = await import('@/app/api/voice/session/route');
    await POST(createRequest({ mode: 'voice_edit', sdp: MOCK_SDP }));

    expect(mockFetch).toHaveBeenCalledWith(
      'https://api.openai.com/v1/realtime/calls',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          'Authorization': 'Bearer test-key',
        }),
        body: expect.any(FormData),
      }),
    );
  });

  it('should return 400 when SDP is missing', async () => {
    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud' }));

    expect(response.status).toBe(400);
  });

  it('should default to read_aloud when mode is invalid', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      text: async () => MOCK_ANSWER_SDP,
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'invalid_mode', sdp: MOCK_SDP }));
    const data = await response.json();

    expect(data.model).toBe('gpt-4o-realtime-preview');
  });

  it('should return 500 when OPENAI_API_KEY is missing', async () => {
    delete process.env.OPENAI_API_KEY;

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud', sdp: MOCK_SDP }));

    expect(response.status).toBe(500);
    const data = await response.json();
    expect(data.error).toContain('configured');
  });

  it('should return error status when OpenAI API fails', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: false,
      status: 400,
      text: async () => '{"error": "bad request"}',
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud', sdp: MOCK_SDP }));

    expect(response.status).toBe(400);
  });
});
