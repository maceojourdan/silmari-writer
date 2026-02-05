import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';

// Mock all voice-related modules
vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    sessionState: 'idle',
    timeRemaining: null,
    connect: vi.fn(),
    disconnect: vi.fn(),
    sendEvent: vi.fn(),
    dataChannel: null,
  }),
}));

vi.mock('@/hooks/useAutoReadAloud', () => ({
  useAutoReadAloud: () => ({
    onNewAssistantMessage: vi.fn(),
    handleResponseDone: vi.fn(),
    resetQueue: vi.fn(),
  }),
}));

vi.mock('@/hooks/useVoiceEdit', () => ({
  useVoiceEdit: () => ({
    startEditing: vi.fn(),
    stopEditing: vi.fn(),
    undo: vi.fn(),
  }),
}));

vi.mock('@/lib/store', () => ({
  useConversationStore: vi.fn(() => ({
    projects: [{ id: 'proj-1', name: 'Test' }],
    activeProjectId: 'proj-1',
    createProject: vi.fn(),
    setActiveProject: vi.fn(),
    addMessage: vi.fn(),
    getMessages: vi.fn(() => [
      { id: 'msg-1', role: 'assistant', content: 'Hello', timestamp: new Date() },
    ]),
    _hasHydrated: true,
    readAloudEnabled: false,
    setReadAloud: vi.fn(),
    voiceSessionState: 'idle',
    editHistory: null,
  })),
}));

vi.mock('@/lib/api', () => ({
  generateResponse: vi.fn(),
}));

vi.mock('@/lib/transcription', () => ({
  transcribeAudio: vi.fn(),
}));

// Mock components that have unresolvable deps
vi.mock('@/components/chat/AudioRecorder', () => ({
  default: vi.fn(() => null),
  __esModule: true,
}));

vi.mock('@/components/chat/FileAttachment', () => ({
  default: vi.fn(() => null),
}));

vi.mock('@/components/chat/ConversationView', () => ({
  default: vi.fn(() => null),
}));

vi.mock('@/components/chat/MessageInput', () => ({
  default: vi.fn(() => null),
}));

vi.mock('@/components/layout/AppLayout', () => ({
  default: vi.fn(({ children }: { children: React.ReactNode }) => <div>{children}</div>),
}));

vi.mock('@/components/layout/ProjectSidebar', () => ({
  default: vi.fn(() => null),
}));

describe('Voice Integration in Page', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should render ReadAloudToggle in conversation area', async () => {
    const { default: HomePage } = await import('@/app/page');
    render(<HomePage />);

    expect(screen.getByRole('button', { name: /read aloud/i })).toBeInTheDocument();
  });

  it('should render VoiceEditPanel in conversation area', async () => {
    const { default: HomePage } = await import('@/app/page');
    render(<HomePage />);

    expect(screen.getByRole('button', { name: /voice edit/i })).toBeInTheDocument();
  });
});
