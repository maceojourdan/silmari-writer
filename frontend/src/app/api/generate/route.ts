import { NextRequest, NextResponse } from 'next/server';
import OpenAI from 'openai';

export const MAX_ROUTE_ATTACHMENTS = 10;
export const MAX_ROUTE_PAYLOAD_BYTES = 25 * 1024 * 1024; // 25 MB

const MAX_RETRIES = 3;
const BASE_RETRY_DELAY_MS = 2000;
const RATE_LIMIT_BASE_DELAY_MS = 10000;

interface Message {
  role: 'user' | 'assistant' | 'system';
  content: string;
}

interface FileAttachment {
  filename: string;
  contentType: string;
  textContent?: string;
  base64Data?: string;
}

type ContentPart =
  | { type: 'text'; text: string }
  | { type: 'image_url'; image_url: { url: string } };

type MessageContent = string | ContentPart[];

const SUPPORTED_IMAGE_PREFIXES = ['image/png', 'image/jpeg', 'image/gif', 'image/webp'];
const SUPPORTED_TEXT_TYPES_SET = new Set(['text/plain', 'application/json']);

function isSupportedAttachment(att: FileAttachment): boolean {
  return SUPPORTED_IMAGE_PREFIXES.includes(att.contentType) || SUPPORTED_TEXT_TYPES_SET.has(att.contentType);
}

function buildUserContent(
  message: string,
  attachments: FileAttachment[]
): MessageContent {
  // Filter to only supported MIME types
  const supported = (attachments || []).filter(isSupportedAttachment);

  if (supported.length === 0) {
    return message;
  }

  const imageAttachments = supported.filter(a => a.contentType.startsWith('image/'));
  const textAttachments = supported.filter(a => !a.contentType.startsWith('image/'));

  // Build text portion: prepend text file contents
  let textContent = message;
  if (textAttachments.length > 0) {
    const fileTexts = textAttachments
      .map(a => `--- ${a.filename} ---\n${a.textContent || ''}`)
      .join('\n\n');
    textContent = `${fileTexts}\n\n${message}`;
  }

  // If no images, return as string
  if (imageAttachments.length === 0) {
    return textContent;
  }

  // Build multipart content array
  const parts: ContentPart[] = [{ type: 'text', text: textContent }];
  for (const img of imageAttachments) {
    if (img.base64Data) {
      parts.push({ type: 'image_url', image_url: { url: img.base64Data } });
    }
  }
  return parts;
}

export async function POST(request: NextRequest) {
  try {
    const { message, history = [], attachments = [] } = await request.json();

    if (!message || typeof message !== 'string') {
      return NextResponse.json(
        { error: 'Invalid message format', code: 'INVALID_MESSAGE' },
        { status: 400 }
      );
    }

    // Validate attachment limits
    if (attachments.length > MAX_ROUTE_ATTACHMENTS) {
      return NextResponse.json(
        { error: `Too many attachments (max ${MAX_ROUTE_ATTACHMENTS})`, code: 'ATTACHMENT_LIMIT' },
        { status: 400 }
      );
    }

    if (attachments.length > 0) {
      let totalPayloadSize = 0;
      for (const att of attachments) {
        totalPayloadSize += (att.base64Data?.length || 0) + (att.textContent?.length || 0);
      }
      if (totalPayloadSize > MAX_ROUTE_PAYLOAD_BYTES) {
        return NextResponse.json(
          { error: 'Attachment payload too large', code: 'PAYLOAD_TOO_LARGE' },
          { status: 400 }
        );
      }
    }

    // Validate API key exists server-side
    const apiKey = process.env.OPENAI_API_KEY;
    if (!apiKey) {
      console.error('OPENAI_API_KEY is not configured');
      return NextResponse.json(
        { error: 'Chat service not configured', code: 'CONFIG_ERROR' },
        { status: 500 }
      );
    }

    // Initialize OpenAI client
    const openai = new OpenAI({ apiKey });

    // Build user content (plain string or multipart with images)
    const userContent = buildUserContent(message, attachments);

    // Format conversation history for OpenAI API
    const messages: Array<{ role: 'system' | 'user' | 'assistant'; content: MessageContent }> = [
      {
        role: 'system',
        content: 'You are a helpful writing assistant. Help users with their writing tasks, provide feedback, and assist with transcription-related queries.',
      },
      ...history.map((msg: Message) => ({
        role: msg.role,
        content: msg.content,
      })),
      {
        role: 'user',
        content: userContent,
      },
    ];

    // Call OpenAI with retry logic
    const response = await generateWithRetry(openai, messages, 0);

    return NextResponse.json({
      content: response,
    });
  } catch (error) {
    console.error('Chat generation error:', error);

    if (error instanceof ChatGenerationError) {
      const statusCodes: Record<string, number> = {
        INVALID_API_KEY: 401,
        RATE_LIMIT: 429,
        NETWORK: 502,
        API_ERROR: 500,
      };

      return NextResponse.json(
        {
          error: error.message,
          code: error.code,
          retryable: error.retryable,
        },
        { status: statusCodes[error.code] || 500 }
      );
    }

    return NextResponse.json(
      { error: 'Failed to generate response', code: 'INTERNAL_ERROR' },
      { status: 500 }
    );
  }
}

class ChatGenerationError extends Error {
  constructor(
    message: string,
    public code: string,
    public retryable: boolean
  ) {
    super(message);
    this.name = 'ChatGenerationError';
  }
}

async function generateWithRetry(
  openai: OpenAI,
  messages: Array<{ role: 'system' | 'user' | 'assistant'; content: MessageContent }>,
  retries: number
): Promise<string> {
  try {
    return await makeOpenAIRequest(openai, messages);
  } catch (error) {
    if (error instanceof ChatGenerationError && error.retryable && retries < MAX_RETRIES) {
      // Use longer delays for rate limit errors
      const baseDelay = error.code === 'RATE_LIMIT'
        ? RATE_LIMIT_BASE_DELAY_MS
        : BASE_RETRY_DELAY_MS;

      // Exponential backoff: baseDelay * 2^retries
      const delay = baseDelay * Math.pow(2, retries);
      console.warn(`Retry ${retries + 1}/${MAX_RETRIES} after ${delay}ms (${error.code})`);
      await new Promise(resolve => setTimeout(resolve, delay));
      return generateWithRetry(openai, messages, retries + 1);
    }
    throw error;
  }
}

async function makeOpenAIRequest(
  openai: OpenAI,
  messages: Array<{ role: 'system' | 'user' | 'assistant'; content: MessageContent }>
): Promise<string> {
  try {
    // Call OpenAI Chat Completions API
    const completion = await openai.chat.completions.create({
      model: 'gpt-4o-mini',
      messages: messages as OpenAI.ChatCompletionMessageParam[],
      temperature: 0.7,
      max_tokens: 2000,
    });

    const content = completion.choices[0]?.message?.content;
    if (!content) {
      throw new ChatGenerationError(
        'No response generated',
        'API_ERROR',
        false
      );
    }

    return content;
  } catch (error: unknown) {
    // Handle OpenAI SDK errors
    if (error && typeof error === 'object' && 'status' in error) {
      const status = (error as { status?: number }).status;
      const message = (error as { message?: string }).message || 'Unknown error';

      switch (status) {
        case 401:
          throw new ChatGenerationError(
            `Invalid API key: ${message}`,
            'INVALID_API_KEY',
            false
          );
        case 429:
          throw new ChatGenerationError(
            `Rate limit exceeded: ${message}`,
            'RATE_LIMIT',
            true
          );
        case 500:
        case 502:
        case 503:
        case 504:
          throw new ChatGenerationError(
            `Server error: ${message}`,
            'API_ERROR',
            true
          );
        default:
          throw new ChatGenerationError(
            `API error: ${message}`,
            'API_ERROR',
            false
          );
      }
    }

    // Network or other errors
    throw new ChatGenerationError(
      `Network error: ${error instanceof Error ? error.message : 'Unknown error'}`,
      'NETWORK',
      true
    );
  }
}
