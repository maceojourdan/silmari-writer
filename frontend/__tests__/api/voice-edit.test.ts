import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { NextRequest } from 'next/server';

// eslint-disable-next-line @typescript-eslint/no-explicit-any
const mockCreate = vi.fn();
vi.mock('openai', () => ({
  default: vi.fn().mockImplementation(function () {
    return {
      chat: {
        completions: {
          create: mockCreate,
        },
      },
    };
  }),
}));

const originalEnv = process.env;

function createRequest(body: Record<string, unknown>): NextRequest {
  return new NextRequest('http://localhost:3000/api/voice/edit', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('POST /api/voice/edit', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.resetModules();
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-key' };
  });

  afterEach(() => {
    process.env = originalEnv;
  });

  it('should apply edit instruction to message content', async () => {
    mockCreate.mockResolvedValueOnce({
      choices: [{
        message: {
          content: JSON.stringify({
            edited_content: 'The quick brown fox jumped gracefully over the lazy dog.',
            edit_summary: 'Added adverb "gracefully"',
          }),
        },
      }],
    });

    const { POST } = await import('@/app/api/voice/edit/route');
    const response = await POST(createRequest({
      instruction: 'Add the word gracefully before "over"',
      messageContent: 'The quick brown fox jumped over the lazy dog.',
      messageId: 'msg-1',
    }));

    const data = await response.json();
    expect(response.status).toBe(200);
    expect(data.editedContent).toBe(
      'The quick brown fox jumped gracefully over the lazy dog.',
    );
    expect(data.editSummary).toBe('Added adverb "gracefully"');
    expect(data.messageId).toBe('msg-1');
  });

  it('should include document context when provided', async () => {
    mockCreate.mockResolvedValueOnce({
      choices: [{
        message: {
          content: JSON.stringify({
            edited_content: 'Updated content',
            edit_summary: 'Applied edit',
          }),
        },
      }],
    });

    const { POST } = await import('@/app/api/voice/edit/route');
    await POST(createRequest({
      instruction: 'Fix the typo in the introduction',
      messageContent: 'The intrduction explains the concept.',
      messageId: 'msg-1',
      documentContext: [
        { messageId: 'msg-0', content: 'Title: My Essay' },
        { messageId: 'msg-1', content: 'The intrduction explains the concept.' },
      ],
    }));

    const callArgs = mockCreate.mock.calls[0][0];
    const systemMessage = callArgs.messages.find(
      (m: { role: string }) => m.role === 'system',
    );
    expect(systemMessage.content).toContain('My Essay');
  });

  it('should return 500 when OPENAI_API_KEY is missing', async () => {
    delete process.env.OPENAI_API_KEY;

    const { POST } = await import('@/app/api/voice/edit/route');
    const response = await POST(createRequest({
      instruction: 'Fix typo',
      messageContent: 'Content',
      messageId: 'msg-1',
    }));

    expect(response.status).toBe(500);
  });

  it('should return 400 when required fields are missing', async () => {
    const { POST } = await import('@/app/api/voice/edit/route');
    const response = await POST(createRequest({
      instruction: 'Fix typo',
    }));

    expect(response.status).toBe(400);
  });
});
