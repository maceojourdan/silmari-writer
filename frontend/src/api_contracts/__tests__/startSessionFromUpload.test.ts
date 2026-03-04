import { beforeEach, describe, expect, it, vi } from 'vitest';
import { StartSessionAlreadyActiveError } from '../startSessionFromUrl';
import {
  StartSessionFromUploadRequestSchema,
  StartSessionFromUploadResponseSchema,
  startSessionFromUpload,
} from '../startSessionFromUpload';

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('startSessionFromUpload API contract', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('validates request schema', () => {
    expect(
      StartSessionFromUploadRequestSchema.safeParse({
        files: [
          {
            filename: 'resume.pdf',
            url: 'https://example.test/resume.pdf',
            mimeType: 'application/pdf',
          },
        ],
      }).success,
    ).toBe(true);
  });

  it('validates response schema', () => {
    expect(
      StartSessionFromUploadResponseSchema.safeParse({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'initialized',
        inputMode: 'file_upload',
        questions: [
          {
            id: 'q-default-1',
            text: 'Question',
            category: 'default',
            position: 0,
          },
        ],
        questionProgress: {
          currentIndex: 0,
          total: 1,
          completed: [],
          activeQuestionId: 'q-default-1',
        },
      }).success,
    ).toBe(true);
  });

  it('uploads files and starts file-upload session', async () => {
    const file = new File(['resume body'], 'resume.pdf', { type: 'application/pdf' });

    mockFetch
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          url: 'https://blob.vercel-storage.com/resume.pdf',
        }),
      })
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          sessionId: '550e8400-e29b-41d4-a716-446655440000',
          state: 'initialized',
          inputMode: 'file_upload',
          questions: [
            {
              id: 'q-default-1',
              text: 'Question',
              category: 'default',
              position: 0,
            },
          ],
          questionProgress: {
            currentIndex: 0,
            total: 1,
            completed: [],
            activeQuestionId: 'q-default-1',
          },
        }),
      });

    const result = await startSessionFromUpload('valid-token', [file]);

    expect(result.sessionId).toBe('550e8400-e29b-41d4-a716-446655440000');
    expect(mockFetch).toHaveBeenCalledTimes(2);
    expect(mockFetch).toHaveBeenNthCalledWith(
      2,
      '/api/session/start-from-upload',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          Authorization: 'Bearer valid-token',
        }),
      }),
    );
  });

  it('throws StartSessionAlreadyActiveError for 409 conflict', async () => {
    const file = new File(['resume body'], 'resume.pdf', { type: 'application/pdf' });

    mockFetch
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          url: 'https://blob.vercel-storage.com/resume.pdf',
        }),
      })
      .mockResolvedValueOnce({
        ok: false,
        status: 409,
        json: async () => ({
          code: 'SESSION_ALREADY_ACTIVE',
          message: 'A session is already active.',
        }),
      });

    await expect(startSessionFromUpload('valid-token', [file])).rejects.toBeInstanceOf(
      StartSessionAlreadyActiveError,
    );
  });
});
