import { beforeEach, describe, expect, it, vi } from 'vitest';
import { getSession } from '../getSession';

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('getSession', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('returns normalized session payload for valid id', async () => {
    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        id: '550e8400-e29b-41d4-a716-446655440000',
        state: 'INIT',
        source: 'answer_session',
        createdAt: '2026-03-02T10:00:00.000Z',
        updatedAt: '2026-03-02T10:00:00.000Z',
      }),
    });

    const result = await getSession('550e8400-e29b-41d4-a716-446655440000');

    expect(mockFetch).toHaveBeenCalledWith('/api/sessions/550e8400-e29b-41d4-a716-446655440000');
    expect(result.id).toBe('550e8400-e29b-41d4-a716-446655440000');
    expect(result.state).toBe('INIT');
  });

  it('throws server error message on non-ok response', async () => {
    mockFetch.mockResolvedValue({
      ok: false,
      status: 404,
      json: async () => ({ code: 'SESSION_NOT_FOUND', message: 'Session not found' }),
    });

    await expect(getSession('550e8400-e29b-41d4-a716-446655440000')).rejects.toThrow('Session not found');
  });

  it('throws when response payload is malformed', async () => {
    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({ id: 'not-a-uuid', state: 'INIT' }),
    });

    await expect(getSession('550e8400-e29b-41d4-a716-446655440000')).rejects.toThrow('Invalid response');
  });
});

