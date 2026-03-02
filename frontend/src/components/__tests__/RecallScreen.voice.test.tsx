import { act, render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { beforeEach, describe, expect, it, vi } from 'vitest';
import RecallScreen from '../RecallScreen';

const SESSION_ID = '550e8400-e29b-41d4-a716-446655440000';

type VoiceEvent = { type: string; [key: string]: unknown };

const mockConnect = vi.fn();
const mockDisconnect = vi.fn();
const mockSetOnEvent = vi.fn();
const mockSubmitVoiceResponse = vi.fn();
const mockOnVoiceResponseSaved = vi.fn();

let mockSessionState: 'idle' | 'connecting' | 'connected' | 'error' = 'idle';
let capturedEventHandler: ((event: VoiceEvent) => void) | null = null;

function emitVoiceEvent(event: VoiceEvent) {
  act(() => {
    capturedEventHandler?.(event);
  });
}

vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    connect: mockConnect,
    disconnect: mockDisconnect,
    sessionState: mockSessionState,
    setOnEvent: mockSetOnEvent,
  }),
}));

vi.mock('@/api_contracts/submitVoiceResponse', () => ({
  submitVoiceResponse: (payload: unknown) => mockSubmitVoiceResponse(payload),
}));

describe('RecallScreen voice session wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSessionState = 'idle';
    capturedEventHandler = null;
    mockConnect.mockResolvedValue(true);
    mockOnVoiceResponseSaved.mockResolvedValue(undefined);
    mockSubmitVoiceResponse.mockResolvedValue({
      session: {
        id: SESSION_ID,
        userId: 'user-123',
        state: 'IN_PROGRESS',
        createdAt: '2026-03-02T00:00:00.000Z',
        updatedAt: '2026-03-02T00:00:01.000Z',
      },
      storyRecord: {
        id: '660e8400-e29b-41d4-a716-446655440001',
        sessionId: SESSION_ID,
        status: 'IN_PROGRESS',
        content: 'content',
        createdAt: '2026-03-02T00:00:00.000Z',
        updatedAt: '2026-03-02T00:00:01.000Z',
      },
    });
    mockSetOnEvent.mockImplementation((callback: ((event: VoiceEvent) => void) | null) => {
      capturedEventHandler = callback;
    });
  });

  it('renders selected story details when provided', () => {
    render(
      <RecallScreen
        selectedStory={{
          id: 'story-001',
          title: 'Led migration',
          summary: 'Migrated a critical service with zero downtime.',
          status: 'CONFIRMED',
          questionId: 'q-001',
        }}
      />,
    );

    expect(screen.getByTestId('selected-story')).toBeInTheDocument();
    expect(screen.getByText('Led migration')).toBeInTheDocument();
  });

  it('connects to the voice model when record is clicked', async () => {
    const user = userEvent.setup();
    render(
      <RecallScreen
        selectedStory={{
          id: 'story-001',
          title: 'Led migration',
          summary: 'Migrated a critical service with zero downtime.',
          status: 'CONFIRMED',
          questionId: 'q-001',
        }}
      />,
    );

    await user.click(screen.getByTestId('record-button'));

    await waitFor(() => {
      expect(mockConnect).toHaveBeenCalledWith(
        'voice_edit',
        expect.objectContaining({
          instructions: expect.stringContaining('Led migration'),
        }),
      );
    });
  });

  it('disconnects an active voice session when record button is pressed while connected', async () => {
    const user = userEvent.setup();
    mockSessionState = 'connected';

    render(<RecallScreen />);

    await user.click(screen.getByTestId('record-button'));

    expect(mockDisconnect).toHaveBeenCalledTimes(1);
    expect(mockConnect).not.toHaveBeenCalled();
  });

  it('shows recoverable error when voice model connection fails', async () => {
    const user = userEvent.setup();
    mockConnect.mockResolvedValue(false);

    render(<RecallScreen />);
    await user.click(screen.getByTestId('record-button'));

    await waitFor(() => {
      expect(screen.getByTestId('voice-model-error')).toHaveTextContent(
        'Unable to start voice model session. Please try again.',
      );
    });
  });

  it('registers and cleans up realtime event handler when connected with sessionId', () => {
    mockSessionState = 'connected';
    const { unmount } = render(<RecallScreen sessionId={SESSION_ID} />);

    expect(mockSetOnEvent).toHaveBeenCalledWith(expect.any(Function));

    unmount();

    expect(mockSetOnEvent).toHaveBeenLastCalledWith(null);
  });

  it('submits final transcript events and invokes refresh callback on success', async () => {
    mockSessionState = 'connected';
    render(
      <RecallScreen
        sessionId={SESSION_ID}
        onVoiceResponseSaved={mockOnVoiceResponseSaved}
      />,
    );

    emitVoiceEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-1',
      transcript: 'Built an onboarding workflow.',
    });

    await waitFor(() => {
      expect(mockSubmitVoiceResponse).toHaveBeenCalledWith({
        sessionId: SESSION_ID,
        transcript: 'Built an onboarding workflow.',
      });
    });

    await waitFor(() => {
      expect(mockOnVoiceResponseSaved).toHaveBeenCalledTimes(1);
      expect(screen.getByTestId('voice-submit-status')).toHaveTextContent('Response saved.');
    });
  });

  it('ignores non-final transcript events', async () => {
    mockSessionState = 'connected';
    render(<RecallScreen sessionId={SESSION_ID} />);

    emitVoiceEvent({
      type: 'conversation.item.input_audio_transcription.delta',
      item_id: 'item-1',
      transcript: 'partial',
    });

    await waitFor(() => {
      expect(mockSubmitVoiceResponse).not.toHaveBeenCalled();
    });
  });

  it('dedupes repeated final transcript events', async () => {
    mockSessionState = 'connected';
    render(<RecallScreen sessionId={SESSION_ID} />);

    const event = {
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-duplicate',
      transcript: 'Resolved an outage in production.',
    };

    emitVoiceEvent(event);
    emitVoiceEvent(event);

    await waitFor(() => {
      expect(mockSubmitVoiceResponse).toHaveBeenCalledTimes(1);
    });
  });

  it('guards against concurrent submissions while one is in flight', async () => {
    mockSessionState = 'connected';

    let resolveRequest: (() => void) | undefined;
    mockSubmitVoiceResponse.mockReturnValue(
      new Promise<void>((resolve) => {
        resolveRequest = () => resolve();
      }),
    );

    render(<RecallScreen sessionId={SESSION_ID} />);

    emitVoiceEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-1',
      transcript: 'First response.',
    });
    emitVoiceEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-2',
      transcript: 'Second response while pending.',
    });

    expect(mockSubmitVoiceResponse).toHaveBeenCalledTimes(1);

    resolveRequest?.();

    await waitFor(() => {
      expect(screen.getByTestId('voice-submit-status')).toHaveTextContent('Response saved.');
    });
  });

  it('shows submit status transitions for saving and error states', async () => {
    mockSessionState = 'connected';

    let resolveRequest: (() => void) | undefined;
    mockSubmitVoiceResponse.mockReturnValueOnce(
      new Promise<void>((resolve) => {
        resolveRequest = () => resolve();
      }),
    );

    render(<RecallScreen sessionId={SESSION_ID} />);

    expect(screen.getByTestId('voice-submit-status')).toHaveTextContent(
      'Listening for your response...',
    );

    emitVoiceEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-save',
      transcript: 'Saving status message.',
    });

    await waitFor(() => {
      expect(screen.getByTestId('voice-submit-status')).toHaveTextContent(
        'Saving your response...',
      );
    });

    resolveRequest?.();

    await waitFor(() => {
      expect(screen.getByTestId('voice-submit-status')).toHaveTextContent('Response saved.');
    });

    mockSubmitVoiceResponse.mockRejectedValueOnce(new Error('boom'));

    emitVoiceEvent({
      type: 'conversation.item.input_audio_transcription.completed',
      item_id: 'item-error',
      transcript: 'Error status message.',
    });

    await waitFor(() => {
      expect(screen.getByTestId('voice-submit-status')).toHaveTextContent(
        'Could not save response. Please try speaking again.',
      );
    });
  });
});
