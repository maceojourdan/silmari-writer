import { beforeEach, describe, expect, it, vi } from 'vitest';
import { SessionErrors } from '@/server/error_definitions/SessionErrors';

vi.mock('@/server/services/InitializeSessionService', () => ({
  InitializeSessionService: {
    createSession: vi.fn(),
  },
}));

import { InitializeSessionService } from '@/server/services/InitializeSessionService';
import { POST } from '../route';

const mockCreateSession = vi.mocked(InitializeSessionService.createSession);

function makeRequest(authToken?: string): Request {
  return new Request('http://localhost/api/session/start-default', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      ...(authToken ? { Authorization: `Bearer ${authToken}` } : {}),
    },
    body: JSON.stringify({}),
  });
}

describe('POST /api/session/start-default', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('returns initialized session payload for default mode', async () => {
    mockCreateSession.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      resume: {
        content: 'Default context',
        name: 'Default',
        wordCount: 2,
      },
      job: {
        title: 'General role context',
        description: 'Default question context',
        sourceType: 'text',
        sourceValue: 'default',
      },
      question: {
        text: 'Question',
      },
      state: 'initialized',
      createdAt: '2026-03-03T00:00:00.000Z',
    });

    const response = await POST(makeRequest('valid-token') as any);
    const data = await response.json();

    expect(response.status).toBe(200);
    expect(data).toMatchObject({
      sessionId: '550e8400-e29b-41d4-a716-446655440000',
      state: 'initialized',
      inputMode: 'default_questions',
    });
    expect(data.questions.length).toBeGreaterThan(0);
    expect(data.questionProgress.total).toBe(data.questions.length);
  });

  it('returns 401 when authorization header is missing', async () => {
    const response = await POST(makeRequest() as any);
    const data = await response.json();

    expect(response.status).toBe(401);
    expect(data.code).toBe('UNAUTHORIZED');
  });

  it('returns 409 for active-session conflict', async () => {
    mockCreateSession.mockRejectedValue(SessionErrors.SessionAlreadyActive());

    const response = await POST(makeRequest('valid-token') as any);
    const data = await response.json();

    expect(response.status).toBe(409);
    expect(data.code).toBe('SESSION_ALREADY_ACTIVE');
  });
});
