import { Message } from './types';
import type { FileContentPayload } from './file-content';

export async function generateResponse(
  userMessage: string,
  conversationHistory: Message[],
  attachments?: FileContentPayload[]
): Promise<string> {
  const body: Record<string, unknown> = {
    message: userMessage,
    history: conversationHistory.slice(-10), // Last 10 messages for context
  };

  if (attachments && attachments.length > 0) {
    body.attachments = attachments;
  }

  const response = await fetch('/api/generate', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });

  if (!response.ok) {
    throw new Error('Failed to generate response');
  }

  const data = await response.json();
  return data.content;
}
