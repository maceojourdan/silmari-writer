import { describe, expect, it, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import WriterPage from '../page';
import { createSession } from '@/api_contracts/createSession';

const mockPush = vi.fn();

vi.mock('next/navigation', () => ({
  useRouter: () => ({
    push: mockPush,
  }),
}));

vi.mock('@/api_contracts/createSession', () => ({
  createSession: vi.fn(),
}));

const mockCreateSession = vi.mocked(createSession);

describe('WriterPage start-session flow', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('navigates to /session/[id] after successful session creation', async () => {
    const user = userEvent.setup();
    mockCreateSession.mockResolvedValue({
      sessionId: '550e8400-e29b-41d4-a716-446655440000',
      state: 'INIT',
    });

    render(<WriterPage />);

    await user.click(screen.getByRole('button', { name: /start voice-assisted session/i }));

    await waitFor(() => {
      expect(mockPush).toHaveBeenCalledWith('/session/550e8400-e29b-41d4-a716-446655440000');
    });
  });

  it('shows an error and keeps user on /writer when session creation fails', async () => {
    const user = userEvent.setup();
    mockCreateSession.mockRejectedValue(new Error('Network failure'));

    render(<WriterPage />);

    await user.click(screen.getByRole('button', { name: /start voice-assisted session/i }));

    await waitFor(() => {
      expect(screen.getByRole('alert')).toHaveTextContent('Network failure');
    });
    expect(mockPush).not.toHaveBeenCalled();
  });
});
