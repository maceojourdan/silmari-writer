import { useCallback, useEffect, useRef } from 'react';
import { useRealtimeSession } from '@/hooks/useRealtimeSession';
import { useConversationStore } from '@/lib/store';
import { VOICE_MODES, createEditEntry } from '@/lib/voice-types';

const EDIT_TOOL = {
  type: 'function' as const,
  name: 'send_edit_instruction',
  description:
    'Send an edit instruction to apply to the document. Call this when the user describes an edit they want to make.',
  parameters: {
    type: 'object',
    properties: {
      instruction: {
        type: 'string',
        description: 'The edit instruction to apply',
      },
      target_message_id: {
        type: 'string',
        description: 'The ID of the message to edit, if specified by the user',
      },
    },
    required: ['instruction'],
  },
};

export function useVoiceEdit() {
  const { connect, disconnect, sendEvent, dataChannel } = useRealtimeSession();
  const {
    activeProjectId,
    replaceMessage,
    getMessages,
    initEditHistory,
    snapshotOriginal,
    pushEdit,
    popEdit,
    clearEditHistory,
  } = useConversationStore();

  const sessionIdRef = useRef<string | null>(null);

  const startEditing = useCallback(async () => {
    if (!activeProjectId) return;

    const sessionId = crypto.randomUUID();
    sessionIdRef.current = sessionId;
    initEditHistory(activeProjectId, sessionId);

    const messages = getMessages(activeProjectId);
    const assistantMessages = messages.filter((m) => m.role === 'assistant');
    const documentPreview = assistantMessages
      .map((m) => `[Message ${m.id}]: ${m.content.slice(0, 200)}...`)
      .join('\n');

    await connect(VOICE_MODES.VOICE_EDIT, {
      instructions: `You are a voice editing assistant. The user will speak edit instructions for their document. When the user describes an edit, call send_edit_instruction with the instruction text.\n\nDOCUMENT MESSAGES:\n${documentPreview}`,
      tools: [EDIT_TOOL],
    });
  }, [activeProjectId, connect, getMessages, initEditHistory]);

  const handleEditInstruction = useCallback(
    async (instruction: string, targetMessageId?: string) => {
      if (!activeProjectId) return;

      const messages = getMessages(activeProjectId);
      const targetMessage = targetMessageId
        ? messages.find((m) => m.id === targetMessageId)
        : messages.filter((m) => m.role === 'assistant').at(-1);

      if (!targetMessage) return;

      snapshotOriginal(targetMessage.id, targetMessage.content);

      const documentContext = messages
        .filter((m) => m.role === 'assistant')
        .map((m) => ({ messageId: m.id, content: m.content }));

      const response = await fetch('/api/voice/edit', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          instruction,
          messageContent: targetMessage.content,
          messageId: targetMessage.id,
          documentContext,
        }),
      });

      if (!response.ok) {
        sendEvent({
          type: 'conversation.item.create',
          item: {
            type: 'message',
            role: 'assistant',
            content: [{ type: 'input_text', text: 'Sorry, I could not apply that edit. Please try again.' }],
          },
        });
        sendEvent({ type: 'response.create', response: { modalities: ['audio'] } });
        return;
      }

      const { editedContent, editSummary, messageId } = await response.json();

      pushEdit(
        createEditEntry({
          messageId,
          editedContent,
          editSummary,
        }),
      );

      replaceMessage(activeProjectId, messageId, {
        ...targetMessage,
        content: editedContent,
      });

      sendEvent({
        type: 'conversation.item.create',
        item: {
          type: 'message',
          role: 'assistant',
          content: [
            {
              type: 'input_text',
              text: `Edit applied: ${editSummary || 'Changes made'}. Here is the updated text: ${editedContent.slice(0, 500)}`,
            },
          ],
        },
      });
      sendEvent({ type: 'response.create', response: { modalities: ['audio'] } });
    },
    [activeProjectId, getMessages, snapshotOriginal, pushEdit, replaceMessage, sendEvent],
  );

  useEffect(() => {
    if (!dataChannel) return;

    const handleMessage = async (event: MessageEvent) => {
      if (typeof event.data !== 'string') return;
      const msg = JSON.parse(event.data);
      if (
        msg.type === 'response.function_call_arguments.done' &&
        msg.name === 'send_edit_instruction'
      ) {
        const args = JSON.parse(msg.arguments);
        await handleEditInstruction(args.instruction, args.target_message_id);
      }
    };

    const listener: EventListener = (event) => {
      void handleMessage(event as MessageEvent);
    };

    dataChannel.addEventListener('message', listener);
    return () => {
      dataChannel.removeEventListener('message', listener);
    };
  }, [dataChannel, handleEditInstruction]);

  const undo = useCallback(() => {
    if (!activeProjectId) return;

    const result = popEdit();
    if (!result) return;

    const messages = getMessages(activeProjectId);
    const targetMessage = messages.find((m) => m.id === result.messageId);
    if (!targetMessage) return;

    replaceMessage(activeProjectId, result.messageId, {
      ...targetMessage,
      content: result.previousContent,
    });
  }, [activeProjectId, popEdit, getMessages, replaceMessage]);

  const stopEditing = useCallback(() => {
    disconnect();
    clearEditHistory();
    sessionIdRef.current = null;
  }, [disconnect, clearEditHistory]);

  return { startEditing, stopEditing, undo };
}
