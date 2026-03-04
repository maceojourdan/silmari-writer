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

function makeRequest(body: unknown, authToken?: string): Request {
  return new Request('http://localhost/api/session/start-from-upload', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      ...(authToken ? { Authorization: `Bearer ${authToken}` } : {}),
    },
    body: JSON.stringify(body),
  });
}

describe('POST /api/session/start-from-upload', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('returns initialized session payload for valid uploaded files', async () => {
    mockCreateSession.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      resume: {
        content: 'Resume context',
        name: 'Resume',
        wordCount: 2,
      },
      job: {
        title: 'Imported role',
        description: 'Job context',
        sourceType: 'text',
        sourceValue: 'uploaded-files',
      },
      question: {
        text: 'Question',
      },
      state: 'initialized',
      createdAt: '2026-03-03T00:00:00.000Z',
    });

    const response = await POST(
      makeRequest(
        {
          files: [
            {
              filename: 'resume.pdf',
              url: 'https://blob.example/resume.pdf',
              mimeType: 'application/pdf',
            },
          ],
        },
        'valid-token',
      ) as any,
    );

    const data = await response.json();
    expect(response.status).toBe(200);
    expect(data).toMatchObject({
      sessionId: '550e8400-e29b-41d4-a716-446655440000',
      state: 'initialized',
      inputMode: 'file_upload',
    });
    expect(data.questions.length).toBeGreaterThan(0);
    expect(data.questionProgress.total).toBe(data.questions.length);
  });

  it('returns 401 when authorization header is missing', async () => {
    const response = await POST(
      makeRequest({
        files: [
          {
            filename: 'resume.pdf',
            url: 'https://blob.example/resume.pdf',
            mimeType: 'application/pdf',
          },
        ],
      }) as any,
    );

    const data = await response.json();
    expect(response.status).toBe(401);
    expect(data.code).toBe('UNAUTHORIZED');
  });

  it('returns 400 for unsupported file type', async () => {
    const response = await POST(
      makeRequest(
        {
          files: [
            {
              filename: 'archive.zip',
              url: 'https://blob.example/archive.zip',
              mimeType: 'application/zip',
            },
          ],
        },
        'valid-token',
      ) as any,
    );

    const data = await response.json();
    expect(response.status).toBe(400);
    expect(data.code).toBe('VALIDATION_ERROR');
  });

  it('returns 409 for active-session conflict', async () => {
    mockCreateSession.mockRejectedValue(SessionErrors.SessionAlreadyActive());

    const response = await POST(
      makeRequest(
        {
          files: [
            {
              filename: 'resume.pdf',
              url: 'https://blob.example/resume.pdf',
              mimeType: 'application/pdf',
            },
          ],
        },
        'valid-token',
      ) as any,
    );

    const data = await response.json();
    expect(response.status).toBe(409);
    expect(data.code).toBe('SESSION_ALREADY_ACTIVE');
  });
});
