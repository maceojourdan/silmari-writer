import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

const mockStartEditing = vi.fn();
const mockStopEditing = vi.fn();
const mockUndo = vi.fn();

let mockSessionState = 'idle';
let mockTimeRemaining: number | null = null;
let mockEditHistory: { edits: unknown[] } | null = null;

vi.mock('@/hooks/useVoiceEdit', () => ({
  useVoiceEdit: () => ({
    startEditing: mockStartEditing,
    stopEditing: mockStopEditing,
    undo: mockUndo,
  }),
}));

vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    get sessionState() { return mockSessionState; },
    get timeRemaining() { return mockTimeRemaining; },
  }),
}));

vi.mock('@/lib/store', () => ({
  useConversationStore: () => ({
    get editHistory() { return mockEditHistory; },
  }),
}));

describe('VoiceEditPanel', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSessionState = 'idle';
    mockTimeRemaining = null;
    mockEditHistory = null;
  });

  it('should render a Start Voice Edit button when idle', async () => {
    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    expect(screen.getByRole('button', { name: /voice edit/i })).toBeInTheDocument();
  });

  it('should call startEditing when Start button is clicked', async () => {
    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    const user = userEvent.setup();
    await user.click(screen.getByRole('button', { name: /voice edit/i }));

    expect(mockStartEditing).toHaveBeenCalled();
  });

  it('should show stop and undo buttons when session is active', async () => {
    mockSessionState = 'connected';
    mockTimeRemaining = 2100;
    mockEditHistory = { edits: [{ messageId: 'msg-1', editedContent: 'text', timestamp: 1 }] };

    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    expect(screen.getByRole('button', { name: /stop/i })).toBeInTheDocument();
    expect(screen.getByRole('button', { name: /undo/i })).toBeInTheDocument();
  });

  it('should disable undo when no edits in history', async () => {
    mockSessionState = 'connected';
    mockTimeRemaining = 2100;
    mockEditHistory = { edits: [] };

    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    expect(screen.getByRole('button', { name: /undo/i })).toBeDisabled();
  });
});
