import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { POST } from '@/app/api/generate/route';
import { NextRequest } from 'next/server';

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('/api/generate', () => {
  const originalEnv = process.env;

  beforeEach(() => {
    vi.clearAllMocks();
    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        output_text: 'Test response from assistant',
      }),
    });
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-key' };
  });

  afterEach(() => {
    process.env = originalEnv;
  });

  it('should generate response for voice transcription with empty history', async () => {
    const request = new NextRequest('http://localhost:3000/api/generate', {
      method: 'POST',
      body: JSON.stringify({
        message: 'Hello, this is a transcribed voice message',
        history: [] // No previous messages
      })
    });

    const response = await POST(request);
    const data = await response.json();

    expect(response.status).toBe(200);
    expect(data.content).toBe('Test response from assistant');
    expect(mockFetch).toHaveBeenCalledWith(
      'https://api.openai.com/v1/responses',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          Authorization: 'Bearer test-key',
        }),
      }),
    );
  });

  it('should generate response for voice transcription with conversation history', async () => {
    const request = new NextRequest('http://localhost:3000/api/generate', {
      method: 'POST',
      body: JSON.stringify({
        message: 'What did I just say?',
        history: [
          { role: 'assistant', content: 'Previous assistant response' }
        ]
      })
    });

    const response = await POST(request);
    const data = await response.json();

    expect(response.status).toBe(200);
    expect(data.content).toBe('Test response from assistant');
  });

  it('should return 400 for missing message', async () => {
    const request = new NextRequest('http://localhost:3000/api/generate', {
      method: 'POST',
      body: JSON.stringify({
        history: []
      })
    });

    const response = await POST(request);
    const data = await response.json();

    expect(response.status).toBe(400);
    expect(data.error).toBe('Invalid message format');
    expect(mockFetch).not.toHaveBeenCalled();
  });

  it('should return 500 when API key is not configured', async () => {
    delete process.env.OPENAI_API_KEY;

    const request = new NextRequest('http://localhost:3000/api/generate', {
      method: 'POST',
      body: JSON.stringify({
        message: 'Test message',
        history: []
      })
    });

    const response = await POST(request);
    const data = await response.json();

    expect(response.status).toBe(500);
    expect(data.error).toBe('Chat service not configured');
    expect(mockFetch).not.toHaveBeenCalled();
  });
});
