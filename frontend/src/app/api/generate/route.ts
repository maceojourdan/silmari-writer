import { NextRequest, NextResponse } from 'next/server';

const MAX_RETRIES = 3;
const BASE_RETRY_DELAY_MS = 2000;
const RATE_LIMIT_BASE_DELAY_MS = 10000;

const SYSTEM_PROMPT = `You are a writing partner who writes for real-world outcomes, not academic exercises.

Before you write anything, figure out what the user is actually trying to accomplish:
- Are they trying to persuade someone? (cold email, pitch, proposal)
- Entertain or engage? (social media, blog post, creative writing)
- Get a reader to take action? (landing page, CTA, fundraising)
- Inform clearly? (documentation, explainer, report)
- Express something personal? (letter, journal, reflection)

Then write for THAT outcome. Match your tone, structure, and word choices to the intent:
- Persuasion → punchy, benefit-driven, specific. No filler.
- Entertainment → conversational, vivid, surprising. Have a voice.
- Call to action → clear, direct, urgent without being desperate.
- Information → organized, scannable, precise. No fluff.
- Personal → authentic, warm, human. Not corporate.

Rules:
- Write like a sharp human, not a committee. No "In today's fast-paced world" or "It's important to note that."
- Use concrete details over vague claims. "Increased signups 40%" beats "significantly improved metrics."
- If light research (recent events, Reddit discussions, industry context) would make the writing better, search the web for it. Don't guess at facts you could look up.
- Vary sentence length. Short sentences punch. Longer ones build rhythm and carry the reader through more complex ideas.
- Cut anything that doesn't earn its place. Every sentence should do work.
- Match the formality to the context. A tweet thread and a board memo need different registers.
- When the user explicitly asks you to search the web, ALWAYS use the web_search_preview tool. Do not refuse or skip the search.`;

interface Message {
  role: 'user' | 'assistant' | 'system';
  content: string;
}

export async function POST(request: NextRequest) {
  try {
    const { message, history = [] } = await request.json();

    if (!message || typeof message !== 'string') {
      return NextResponse.json(
        { error: 'Invalid message format', code: 'INVALID_MESSAGE' },
        { status: 400 }
      );
    }

    const apiKey = process.env.OPENAI_API_KEY;
    if (!apiKey) {
      console.error('OPENAI_API_KEY is not configured');
      return NextResponse.json(
        { error: 'Chat service not configured', code: 'CONFIG_ERROR' },
        { status: 500 }
      );
    }

    // Build input for the Responses API
    const input: Array<{ role: string; content: string }> = [
      { role: 'system', content: SYSTEM_PROMPT },
      ...history.map((msg: Message) => ({
        role: msg.role,
        content: msg.content,
      })),
      { role: 'user', content: message },
    ];

    const response = await generateWithRetry(apiKey, input, 0);

    return NextResponse.json({ content: response });
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
  apiKey: string,
  input: Array<{ role: string; content: string }>,
  retries: number
): Promise<string> {
  try {
    return await makeOpenAIRequest(apiKey, input);
  } catch (error) {
    if (error instanceof ChatGenerationError && error.retryable && retries < MAX_RETRIES) {
      const baseDelay = error.code === 'RATE_LIMIT'
        ? RATE_LIMIT_BASE_DELAY_MS
        : BASE_RETRY_DELAY_MS;

      const delay = baseDelay * Math.pow(2, retries);
      console.warn(`Retry ${retries + 1}/${MAX_RETRIES} after ${delay}ms (${error.code})`);
      await new Promise(resolve => setTimeout(resolve, delay));
      return generateWithRetry(apiKey, input, retries + 1);
    }
    throw error;
  }
}

async function makeOpenAIRequest(
  apiKey: string,
  input: Array<{ role: string; content: string }>
): Promise<string> {
  try {
    const res = await fetch('https://api.openai.com/v1/responses', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${apiKey}`,
      },
      body: JSON.stringify({
        model: 'gpt-5.2-pro',
        input,
        tools: [{ type: 'web_search_preview' }],
        temperature: 0.7,
        max_output_tokens: 4096,
      }),
    });

    if (!res.ok) {
      const errorBody = await res.text();
      const errorMessage = (() => {
        try { return JSON.parse(errorBody)?.error?.message || errorBody; }
        catch { return errorBody; }
      })();

      switch (res.status) {
        case 401:
          throw new ChatGenerationError(
            `Invalid API key: ${errorMessage}`,
            'INVALID_API_KEY',
            false
          );
        case 429:
          throw new ChatGenerationError(
            `Rate limit exceeded: ${errorMessage}`,
            'RATE_LIMIT',
            true
          );
        case 500:
        case 502:
        case 503:
        case 504:
          throw new ChatGenerationError(
            `Server error: ${errorMessage}`,
            'API_ERROR',
            true
          );
        default:
          throw new ChatGenerationError(
            `API error (${res.status}): ${errorMessage}`,
            'API_ERROR',
            false
          );
      }
    }

    const data = await res.json();

    // Responses API returns output as an array of items
    // Extract text content from output_text or from output items
    if (data.output_text) {
      return data.output_text;
    }

    const textContent = data.output
      ?.filter((item: { type: string }) => item.type === 'message')
      ?.flatMap((item: { content: Array<{ type: string; text: string }> }) => item.content)
      ?.filter((block: { type: string }) => block.type === 'output_text')
      ?.map((block: { text: string }) => block.text)
      ?.join('');

    if (!textContent) {
      throw new ChatGenerationError(
        'No response generated',
        'API_ERROR',
        false
      );
    }

    return textContent;
  } catch (error: unknown) {
    if (error instanceof ChatGenerationError) throw error;

    throw new ChatGenerationError(
      `Network error: ${error instanceof Error ? error.message : 'Unknown error'}`,
      'NETWORK',
      true
    );
  }
}
