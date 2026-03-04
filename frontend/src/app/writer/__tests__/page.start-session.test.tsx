import { describe, expect, it, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import WriterPage from '../page';
import { startSessionFromUrl } from '@/api_contracts/startSessionFromUrl';

const mockPush = vi.fn();

vi.mock('next/navigation', () => ({
  useRouter: () => ({
    push: mockPush,
  }),
}));

vi.mock('@/api_contracts/startSessionFromUrl', () => ({
  startSessionFromUrl: vi.fn(),
}));

const mockStartSessionFromUrl = vi.mocked(startSessionFromUrl);
const sourceUrl = 'https://example.greenhouse.io/job/123';

describe('WriterPage start-session flow', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('renders and switches start input modes', async () => {
    const user = userEvent.setup();

    render(<WriterPage />);

    expect(screen.getByTestId('input-mode-url')).toHaveAttribute('aria-pressed', 'true');
    expect(screen.getByLabelText(/job posting url/i)).toBeInTheDocument();

    await user.click(screen.getByTestId('input-mode-file_upload'));
    expect(screen.getByTestId('input-mode-file_upload')).toHaveAttribute('aria-pressed', 'true');
    expect(screen.queryByLabelText(/job posting url/i)).not.toBeInTheDocument();
    expect(screen.getByTestId('input-mode-panel-file_upload')).toBeInTheDocument();

    await user.click(screen.getByTestId('input-mode-default_questions'));
    expect(screen.getByTestId('input-mode-default_questions')).toHaveAttribute('aria-pressed', 'true');
    expect(screen.getByTestId('input-mode-panel-default_questions')).toBeInTheDocument();
  });

  it('navigates to /session/[id] after successful session creation', async () => {
    const user = userEvent.setup();
    mockStartSessionFromUrl.mockResolvedValue({
      sessionId: '550e8400-e29b-41d4-a716-446655440000',
      state: 'initialized',
      canonicalUrl: sourceUrl,
      contextSummary: 'Context extracted from example.greenhouse.io (direct URL).',
    });

    render(<WriterPage />);

    await user.type(screen.getByLabelText(/job posting url/i), sourceUrl);
    await user.click(screen.getByRole('button', { name: /start voice-assisted session/i }));

    await waitFor(() => {
      expect(mockPush).toHaveBeenCalledWith('/session/550e8400-e29b-41d4-a716-446655440000');
    });
  });

  it('shows an error and keeps user on /writer when session creation fails', async () => {
    const user = userEvent.setup();
    mockStartSessionFromUrl.mockRejectedValue(new Error('Network failure'));

    render(<WriterPage />);

    await user.type(screen.getByLabelText(/job posting url/i), sourceUrl);
    await user.click(screen.getByRole('button', { name: /start voice-assisted session/i }));

    await waitFor(() => {
      expect(screen.getByRole('alert')).toHaveTextContent('Network failure');
    });
    expect(mockPush).not.toHaveBeenCalled();
  });

  it('requires URL input before starting session', async () => {
    const user = userEvent.setup();

    render(<WriterPage />);

    await user.click(screen.getByRole('button', { name: /start voice-assisted session/i }));

    expect(screen.getByRole('alert')).toHaveTextContent('Paste a job URL to continue.');
    expect(mockStartSessionFromUrl).not.toHaveBeenCalled();
  });
});
