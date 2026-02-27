import { Message } from './types';
import type { FileContentPayload } from './file-content';

export async function generateResponse(
  userMessage: string,
  conversationHistory: Message[],
  attachments?: FileContentPayload[],
): Promise<string> {
  const body: Record<string, unknown> = {
    message: userMessage,
    history: conversationHistory.slice(-10).map(msg => ({
      role: msg.role,
      content: msg.content,
    })), // Last 10 messages for context
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
    const errorData = await response.json().catch(() => ({}));
    const errorMessage = errorData.error || 'Failed to generate response';
    console.error('Generate API error:', {
      status: response.status,
      error: errorMessage,
      code: errorData.code,
    });
    throw new Error(errorMessage);
  }

  const data = await response.json();
  return data.content;
}
