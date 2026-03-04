import { beforeEach, describe, expect, it, vi } from 'vitest';
import { StartSessionAlreadyActiveError } from '../startSessionFromUrl';
import {
  StartSessionDefaultQuestionsResponseSchema,
  startSessionDefaultQuestions,
} from '../startSessionDefaultQuestions';

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('startSessionDefaultQuestions API contract', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('validates response schema', () => {
    expect(
      StartSessionDefaultQuestionsResponseSchema.safeParse({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'initialized',
        inputMode: 'default_questions',
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

  it('starts default-questions session', async () => {
    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        sessionId: '550e8400-e29b-41d4-a716-446655440000',
        state: 'initialized',
        inputMode: 'default_questions',
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

    const result = await startSessionDefaultQuestions('valid-token');

    expect(result.inputMode).toBe('default_questions');
    expect(mockFetch).toHaveBeenCalledWith(
      '/api/session/start-default',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          Authorization: 'Bearer valid-token',
        }),
      }),
    );
  });

  it('throws StartSessionAlreadyActiveError for 409 conflict', async () => {
    mockFetch.mockResolvedValue({
      ok: false,
      status: 409,
      json: async () => ({
        code: 'SESSION_ALREADY_ACTIVE',
        message: 'A session is already active.',
      }),
    });

    await expect(startSessionDefaultQuestions('valid-token')).rejects.toBeInstanceOf(
      StartSessionAlreadyActiveError,
    );
  });
});
