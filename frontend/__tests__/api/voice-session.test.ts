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

describe('POST /api/voice/session', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.resetModules();
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-key' };
  });

  afterEach(() => {
    process.env = originalEnv;
  });

  it('should return ephemeral token for read_aloud mode', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ client_secret: 'ek_test_token_123', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud' }));
    const data = await response.json();

    expect(response.status).toBe(200);
    expect(data.token).toBe('ek_test_token_123');
    expect(data.model).toBe('gpt-4o-realtime-preview');
    expect(data.sessionLimitMinutes).toBe(60);
  });

  it('should use gpt-4o-realtime-preview model for voice_edit mode', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ client_secret: 'ek_edit_token_456', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({
      mode: 'voice_edit',
      instructions: 'Edit the document',
      tools: [{ type: 'function', name: 'send_edit_instruction' }],
    }));
    const data = await response.json();

    expect(data.model).toBe('gpt-4o-realtime-preview');

    // Verify OpenAI was called with correct GA endpoint and wrapped body
    expect(mockFetch).toHaveBeenCalledWith(
      'https://api.openai.com/v1/realtime/client_secrets',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          'Authorization': 'Bearer test-key',
        }),
        body: expect.stringContaining('gpt-4o-realtime-preview'),
      }),
    );
  });

  it('should send correct GA session config format', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ client_secret: 'ek_token', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    await POST(createRequest({ mode: 'read_aloud' }));

    const fetchBody = JSON.parse(mockFetch.mock.calls[0][1].body);
    expect(fetchBody.session.type).toBe('realtime');
    expect(fetchBody.session.model).toBe('gpt-4o-realtime-preview');
    expect(fetchBody.session.audio).toEqual({ output: { voice: 'alloy' } });
  });

  it('should default to read_aloud when mode is invalid', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ client_secret: 'ek_token', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'invalid_mode' }));
    const data = await response.json();

    expect(data.model).toBe('gpt-4o-realtime-preview');
  });

  it('should return 500 when OPENAI_API_KEY is missing', async () => {
    delete process.env.OPENAI_API_KEY;

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud' }));

    expect(response.status).toBe(500);
    const data = await response.json();
    expect(data.error).toContain('configured');
  });

  it('should return 502 when OpenAI API fails', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: false,
      status: 500,
      json: async () => ({ error: { message: 'Internal Server Error' } }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud' }));

    expect(response.status).toBe(502);
  });
});
