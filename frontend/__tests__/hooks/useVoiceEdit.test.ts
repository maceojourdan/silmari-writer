import { describe, it, expect, vi, beforeEach } from 'vitest';
import { renderHook, act } from '@testing-library/react';

const mockConnect = vi.fn();
const mockDisconnect = vi.fn();
const mockSendEvent = vi.fn();
const mockAddEventListener = vi.fn();
const mockRemoveEventListener = vi.fn();
let mockMessageListener: ((event: MessageEvent) => void) | null = null;

vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    sessionState: 'connected',
    timeRemaining: 2000,
    connect: mockConnect,
    disconnect: mockDisconnect,
    sendEvent: mockSendEvent,
    dataChannel: {
      addEventListener: mockAddEventListener.mockImplementation((type: string, listener: EventListener) => {
        if (type === 'message') {
          mockMessageListener = listener as unknown as (event: MessageEvent) => void;
        }
      }),
      removeEventListener: mockRemoveEventListener.mockImplementation((type: string, listener: EventListener) => {
        if (type === 'message' && mockMessageListener === listener) {
          mockMessageListener = null;
        }
      }),
    },
  }),
}));

const mockReplaceMessage = vi.fn();
const mockInitEditHistory = vi.fn();
const mockSnapshotOriginal = vi.fn();
const mockPushEdit = vi.fn();
const mockPopEdit = vi.fn();
const mockClearEditHistory = vi.fn();
const mockStoreGetState = vi.fn();

vi.mock('@/lib/store', () => ({
  useConversationStore: Object.assign(
    vi.fn(() => ({
      activeProjectId: 'proj-1',
      replaceMessage: mockReplaceMessage,
      initEditHistory: mockInitEditHistory,
      snapshotOriginal: mockSnapshotOriginal,
      pushEdit: mockPushEdit,
      popEdit: mockPopEdit,
      clearEditHistory: mockClearEditHistory,
      getMessages: vi.fn(() => [
        { id: 'msg-1', role: 'assistant', content: 'Original text', timestamp: new Date() },
      ]),
    })),
    { getState: mockStoreGetState },
  ),
}));

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('useVoiceEdit', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockMessageListener = null;
    mockStoreGetState.mockReturnValue({ voiceSessionState: 'connected' });
    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        editedContent: 'Edited text',
        editSummary: 'Changed something',
        messageId: 'msg-1',
      }),
    });
  });

  it('should start a voice edit session with document context', async () => {
    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    const { result } = renderHook(() => useVoiceEdit());

    await act(async () => {
      await result.current.startEditing();
    });

    expect(mockConnect).toHaveBeenCalledWith('voice_edit', expect.objectContaining({
      instructions: expect.stringContaining('editing assistant'),
      tools: expect.arrayContaining([
        expect.objectContaining({ name: 'send_edit_instruction' }),
      ]),
    }));
    expect(mockInitEditHistory).toHaveBeenCalledWith('proj-1', expect.any(String));
  });

  it('should pass target message context to voice edit instructions', async () => {
    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    const { result } = renderHook(() => useVoiceEdit());

    await act(async () => {
      await result.current.startEditing({
        targetMessageId: 'msg-1',
        targetMessageContent: 'Original text',
      });
    });

    expect(mockConnect).toHaveBeenCalledWith(
      'voice_edit',
      expect.objectContaining({
        instructions: expect.stringContaining('TARGET MESSAGE ID: msg-1'),
      }),
    );

    const [, options] = mockConnect.mock.calls[0];
    expect(options.instructions).toContain('Original text');
  });

  it('should handle send_edit_instruction function call from Realtime API', async () => {
    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    renderHook(() => useVoiceEdit());

    const functionCallEvent = {
      data: JSON.stringify({
        type: 'response.function_call_arguments.done',
        name: 'send_edit_instruction',
        arguments: JSON.stringify({
          instruction: 'Fix the typo',
          target_message_id: 'msg-1',
        }),
      }),
    };

    await act(async () => {
      mockMessageListener?.(functionCallEvent as unknown as MessageEvent);
    });

    expect(mockFetch).toHaveBeenCalledWith('/api/voice/edit', expect.any(Object));
    expect(mockSnapshotOriginal).toHaveBeenCalledWith('msg-1', 'Original text');
    expect(mockPushEdit).toHaveBeenCalledWith(expect.objectContaining({
      messageId: 'msg-1',
      editedContent: 'Edited text',
    }));
    expect(mockReplaceMessage).toHaveBeenCalled();
  });

  it('should undo the last edit', async () => {
    mockPopEdit.mockReturnValueOnce({
      messageId: 'msg-1',
      previousContent: 'Original text',
    });

    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    const { result } = renderHook(() => useVoiceEdit());

    act(() => {
      result.current.undo();
    });

    expect(mockPopEdit).toHaveBeenCalled();
    expect(mockReplaceMessage).toHaveBeenCalledWith(
      'proj-1',
      'msg-1',
      expect.objectContaining({ content: 'Original text' }),
    );
  });

  it('should clean up edit history on stop', async () => {
    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    const { result } = renderHook(() => useVoiceEdit());

    act(() => {
      result.current.stopEditing();
    });

    expect(mockDisconnect).toHaveBeenCalled();
    expect(mockClearEditHistory).toHaveBeenCalled();
  });
});
