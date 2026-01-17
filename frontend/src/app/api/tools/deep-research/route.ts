import { NextRequest, NextResponse } from 'next/server';
import type {
  DeepResearchModel,
  DeepResearchDepth,
  ReasoningSummary,
  DeepResearchErrorCode,
  DeepResearchJobStatus,
  DeepResearchMessage,
  DeepResearchRequest,
  DeepResearchApiResponse,
  DeepResearchResult,
  DeepResearchCitation,
  DeepResearchOptions,
} from '@/lib/types';

// Constants
const OPENAI_API_URL = 'https://api.openai.com/v1/responses';
const MAX_TEXT_LENGTH = 32000;
const REQUEST_TIMEOUT_MS = 120000; // 2 minutes for non-background mode

// Model selection based on depth
const MODEL_MAP: Record<DeepResearchDepth, DeepResearchModel> = {
  quick: 'o4-mini-deep-research-2025-06-26',
  thorough: 'o3-deep-research-2025-06-26',
};

// Default reasoning summary based on depth
const DEFAULT_REASONING_MAP: Record<DeepResearchDepth, ReasoningSummary> = {
  quick: 'auto',
  thorough: 'detailed',
};

// Error response helper
class DeepResearchApiError extends Error {
  constructor(
    message: string,
    public code: DeepResearchErrorCode,
    public retryable: boolean,
    public statusCode: number
  ) {
    super(message);
    this.name = 'DeepResearchApiError';
  }
}

// Validation functions
function validateQuery(query: unknown): string {
  if (!query || typeof query !== 'string') {
    throw new DeepResearchApiError(
      'Query is required and must be a string',
      'VALIDATION_ERROR',
      false,
      400
    );
  }

  const trimmed = query.trim();
  if (trimmed.length === 0) {
    throw new DeepResearchApiError(
      'Query cannot be empty or whitespace only',
      'VALIDATION_ERROR',
      false,
      400
    );
  }

  if (trimmed.length > MAX_TEXT_LENGTH) {
    throw new DeepResearchApiError(
      `Query exceeds maximum length of 32,000 characters`,
      'VALIDATION_ERROR',
      false,
      400
    );
  }

  return trimmed;
}

function validateDepth(depth: unknown): DeepResearchDepth {
  if (depth === undefined || depth === null) {
    return 'quick'; // Default
  }

  if (depth !== 'quick' && depth !== 'thorough') {
    throw new DeepResearchApiError(
      'Depth must be "quick" or "thorough"',
      'VALIDATION_ERROR',
      false,
      400
    );
  }

  return depth as DeepResearchDepth;
}

function validateReasoningSummary(
  summary: unknown,
  defaultValue: ReasoningSummary
): ReasoningSummary {
  if (summary === undefined || summary === null) {
    return defaultValue;
  }

  if (summary !== 'auto' && summary !== 'detailed') {
    throw new DeepResearchApiError(
      'Reasoning summary must be "auto" or "detailed"',
      'VALIDATION_ERROR',
      false,
      400
    );
  }

  return summary as ReasoningSummary;
}

function validateDeveloperInstructions(instructions: unknown): string | undefined {
  if (instructions === undefined || instructions === null) {
    return undefined;
  }

  if (typeof instructions !== 'string') {
    throw new DeepResearchApiError(
      'Developer instructions must be a string',
      'VALIDATION_ERROR',
      false,
      400
    );
  }

  const trimmed = instructions.trim();
  if (trimmed.length === 0) {
    return undefined;
  }

  if (trimmed.length > MAX_TEXT_LENGTH) {
    throw new DeepResearchApiError(
      `Developer instructions exceed maximum length of 32,000 characters`,
      'VALIDATION_ERROR',
      false,
      400
    );
  }

  return trimmed;
}

// Build input messages array
function buildInputMessages(
  query: string,
  developerInstructions?: string
): DeepResearchMessage[] {
  const messages: DeepResearchMessage[] = [];

  // Developer messages come first
  if (developerInstructions) {
    messages.push({
      role: 'developer',
      content: [{ type: 'input_text', text: developerInstructions }],
    });
  }

  // User query
  messages.push({
    role: 'user',
    content: [{ type: 'input_text', text: query }],
  });

  return messages;
}

// Build the request payload
function buildRequestPayload(
  model: DeepResearchModel,
  input: DeepResearchMessage[],
  reasoningSummary: ReasoningSummary,
  background: boolean
): DeepResearchRequest {
  return {
    model,
    input,
    reasoning: { summary: reasoningSummary },
    background,
  };
}

// Process API response into result format
function processApiResponse(response: DeepResearchApiResponse): DeepResearchResult {
  // Extract text from output
  let text = '';
  const citations: DeepResearchCitation[] = [];

  if (response.output) {
    for (const outputItem of response.output) {
      if (outputItem.type === 'message' && outputItem.content) {
        for (const contentBlock of outputItem.content) {
          if (contentBlock.type === 'output_text') {
            text += contentBlock.text;
            if (contentBlock.annotations) {
              citations.push(...contentBlock.annotations);
            }
          }
        }
      }
    }
  }

  // Extract reasoning steps
  const reasoningSteps: Array<{ id: string; text: string }> = [];
  if (response.reasoning) {
    for (const step of response.reasoning) {
      if (step.type === 'reasoning' && step.summary) {
        const summaryText = step.summary
          .filter((s) => s.type === 'summary_text')
          .map((s) => s.text)
          .join(' ');
        reasoningSteps.push({ id: step.id, text: summaryText });
      }
    }
  }

  // Process usage
  const usage = response.usage
    ? {
        inputTokens: response.usage.input_tokens,
        outputTokens: response.usage.output_tokens,
        reasoningTokens: response.usage.reasoning_tokens,
      }
    : undefined;

  return { text, citations, reasoningSteps, usage };
}

// Handle API errors
function handleApiError(status: number, errorData: { error?: { message?: string; code?: string } }): never {
  const message = errorData?.error?.message || 'Unknown API error';

  switch (status) {
    case 401:
      throw new DeepResearchApiError(
        `Invalid API key: ${message}`,
        'INVALID_API_KEY',
        false,
        401
      );
    case 429:
      throw new DeepResearchApiError(
        `Rate limit exceeded: ${message}`,
        'RATE_LIMIT',
        true,
        429
      );
    case 500:
    case 502:
    case 503:
    case 504:
      throw new DeepResearchApiError(
        `Server error: ${message}`,
        'API_ERROR',
        true,
        status
      );
    default:
      throw new DeepResearchApiError(
        `API error: ${message}`,
        'API_ERROR',
        false,
        status
      );
  }
}

// Main POST handler
export async function POST(request: NextRequest) {
  try {
    // Validate API key
    const apiKey = process.env.OPENAI_API_KEY;
    if (!apiKey) {
      console.error('OPENAI_API_KEY is not configured');
      return NextResponse.json(
        { error: 'Deep Research service not configured', code: 'CONFIG_ERROR' },
        { status: 500 }
      );
    }

    // Parse request body
    const body = await request.json() as DeepResearchOptions & { background?: boolean };

    // Validate inputs
    const query = validateQuery(body.query);
    const depth = validateDepth(body.depth);
    const defaultReasoning = DEFAULT_REASONING_MAP[depth];
    const reasoningSummary = validateReasoningSummary(body.reasoningSummary, defaultReasoning);
    const developerInstructions = validateDeveloperInstructions(body.developerInstructions);

    // Determine if background mode (default true)
    const background = body.background !== false;

    // Select model based on depth
    const model = MODEL_MAP[depth];

    // Build request
    const input = buildInputMessages(query, developerInstructions);
    const payload = buildRequestPayload(model, input, reasoningSummary, background);

    // Log request (timing and model)
    const startTime = Date.now();
    console.log(`[Deep Research] Starting request - model: ${model}, background: ${background}`);

    // Make API request
    let apiResponse: Response;
    try {
      const controller = new AbortController();
      const timeoutId = setTimeout(() => controller.abort(), REQUEST_TIMEOUT_MS);

      apiResponse = await fetch(OPENAI_API_URL, {
        method: 'POST',
        headers: {
          'Authorization': `Bearer ${apiKey}`,
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(payload),
        signal: controller.signal,
      });

      clearTimeout(timeoutId);
    } catch (error) {
      if (error instanceof Error && error.name === 'AbortError') {
        throw new DeepResearchApiError(
          'Request timed out',
          'TIMEOUT',
          true,
          504
        );
      }
      throw new DeepResearchApiError(
        `Network error: ${error instanceof Error ? error.message : 'Unknown error'}`,
        'NETWORK',
        true,
        502
      );
    }

    // Handle non-OK responses
    if (!apiResponse.ok) {
      const errorData = await apiResponse.json().catch(() => ({}));
      handleApiError(apiResponse.status, errorData);
    }

    // Parse response
    const data = await apiResponse.json() as DeepResearchApiResponse;

    // Log completion
    const duration = Date.now() - startTime;
    console.log(`[Deep Research] Request completed - duration: ${duration}ms, status: ${data.status}`);

    // Handle background mode response
    if (background && data.status === 'pending') {
      return NextResponse.json(
        {
          jobId: data.id,
          status: data.status as DeepResearchJobStatus,
          statusUrl: `/api/tools/deep-research/${data.id}/status`,
          createdAt: new Date().toISOString(),
          model,
        },
        { status: 202 }
      );
    }

    // Handle completed response (non-background mode or already completed)
    if (data.status === 'completed') {
      const result = processApiResponse(data);
      return NextResponse.json(result, { status: 200 });
    }

    // Handle processing state (shouldn't happen in non-background mode)
    return NextResponse.json(
      {
        jobId: data.id,
        status: data.status,
        statusUrl: `/api/tools/deep-research/${data.id}/status`,
        createdAt: new Date().toISOString(),
        model,
      },
      { status: 202 }
    );
  } catch (error) {
    console.error('[Deep Research] Error:', error);

    if (error instanceof DeepResearchApiError) {
      return NextResponse.json(
        {
          error: error.message,
          code: error.code,
          retryable: error.retryable,
        },
        { status: error.statusCode }
      );
    }

    return NextResponse.json(
      { error: 'Internal server error', code: 'API_ERROR', retryable: false },
      { status: 500 }
    );
  }
}
