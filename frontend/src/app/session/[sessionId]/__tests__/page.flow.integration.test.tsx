import { beforeEach, afterEach, describe, expect, it, vi } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import SessionPage from '../page';
import { getSession } from '@/api_contracts/getSession';

vi.mock('@/api_contracts/getSession', () => ({
  getSession: vi.fn(),
}));

const mockGetSession = vi.mocked(getSession);

const sessionId = '550e8400-e29b-41d4-a716-446655440000';
const routeParams = { sessionId } as unknown as Promise<{ sessionId: string }>;

describe('/session/[sessionId] flow integration', () => {
  const mockFetch = vi.fn();

  beforeEach(() => {
    vi.clearAllMocks();
    vi.stubGlobal('fetch', mockFetch);
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  it('advances review -> finalize -> finalized module controls', async () => {
    const user = userEvent.setup();
    mockGetSession.mockResolvedValue({
      id: sessionId,
      state: 'DRAFT',
      source: 'session',
      createdAt: '2026-03-02T10:00:00.000Z',
      updatedAt: '2026-03-02T10:00:00.000Z',
    });

    mockFetch
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          entity: {
            id: `content-${sessionId}`,
            status: 'APPROVED',
            workflowStage: 'FINALIZE',
            createdAt: '2026-03-02T10:00:00.000Z',
            updatedAt: '2026-03-02T10:00:00.000Z',
          },
          workflowStage: 'FINALIZE',
        }),
      })
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          id: sessionId,
          finalized: true,
          editable: false,
        }),
      });

    render(<SessionPage params={routeParams} />);

    expect(await screen.findByTestId('session-page')).toBeInTheDocument();

    await user.click(screen.getByTestId(`content-item-content-${sessionId}`));
    await user.click(screen.getByRole('button', { name: /approve/i }));

    await waitFor(() => {
      expect(screen.getByRole('button', { name: /finalize answer/i })).toBeInTheDocument();
    });

    await user.click(screen.getByRole('button', { name: /finalize answer/i }));

    await waitFor(() => {
      expect(screen.getByRole('button', { name: /copy to clipboard/i })).toBeInTheDocument();
    });
  });

  it('keeps user in draft stage when review approval fails', async () => {
    const user = userEvent.setup();
    mockGetSession.mockResolvedValue({
      id: sessionId,
      state: 'DRAFT',
      source: 'session',
      createdAt: '2026-03-02T10:00:00.000Z',
      updatedAt: '2026-03-02T10:00:00.000Z',
    });

    mockFetch.mockResolvedValueOnce({
      ok: false,
      status: 500,
      json: async () => ({
        code: 'INTERNAL_ERROR',
        message: 'An unexpected error occurred',
      }),
    });

    render(<SessionPage params={routeParams} />);

    expect(await screen.findByTestId('session-page')).toBeInTheDocument();

    await user.click(screen.getByTestId(`content-item-content-${sessionId}`));
    await user.click(screen.getByRole('button', { name: /approve/i }));

    await waitFor(() => {
      expect(screen.getByTestId('error-notification')).toBeInTheDocument();
    });

    expect(screen.getByTestId('review-workflow-module')).toBeInTheDocument();
    expect(screen.queryByRole('button', { name: /finalize answer/i })).not.toBeInTheDocument();
  });

  it('shows recoverable error UI when session hydration fails', async () => {
    mockGetSession.mockRejectedValue(new Error('Session not found'));

    render(<SessionPage params={routeParams} />);

    const errorView = await screen.findByTestId('session-page-error');
    expect(errorView).toBeInTheDocument();
    expect(errorView).toHaveTextContent('Session not found');
  });
});
