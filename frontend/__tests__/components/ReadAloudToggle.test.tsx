import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

const mockConnect = vi.fn();
const mockDisconnect = vi.fn();

vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    sessionState: 'idle',
    timeRemaining: null,
    connect: mockConnect,
    disconnect: mockDisconnect,
  }),
}));

const mockSetReadAloud = vi.fn();
vi.mock('@/lib/store', () => ({
  useConversationStore: vi.fn(() => ({
    readAloudEnabled: false,
    setReadAloud: mockSetReadAloud,
  })),
}));

describe('ReadAloudToggle', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should render a toggle button with "Read Aloud" label', async () => {
    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    expect(screen.getByRole('button', { name: /read aloud/i })).toBeInTheDocument();
  });

  it('should show OFF state by default', async () => {
    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    const button = screen.getByRole('button', { name: /read aloud/i });
    expect(button).toHaveAttribute('aria-pressed', 'false');
  });

  it('should call setReadAloud(true) and connect on click when OFF', async () => {
    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    const user = userEvent.setup();
    await user.click(screen.getByRole('button', { name: /read aloud/i }));

    expect(mockSetReadAloud).toHaveBeenCalledWith(true);
    expect(mockConnect).toHaveBeenCalledWith('read_aloud');
  });

  it('should show ON state and disconnect on click when ON', async () => {
    vi.mocked(await import('@/lib/store')).useConversationStore.mockReturnValue({
      readAloudEnabled: true,
      setReadAloud: mockSetReadAloud,
    } as unknown as ReturnType<typeof import('@/lib/store').useConversationStore>);

    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    const user = userEvent.setup();
    await user.click(screen.getByRole('button', { name: /read aloud/i }));

    expect(mockSetReadAloud).toHaveBeenCalledWith(false);
    expect(mockDisconnect).toHaveBeenCalled();
  });
});
