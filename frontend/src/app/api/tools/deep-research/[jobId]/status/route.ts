import { NextRequest, NextResponse } from 'next/server';
import type {
  DeepResearchApiResponse,
  DeepResearchResult,
  DeepResearchCitation,
  DeepResearchJobStatus,
  DeepResearchProgress,
  DeepResearchErrorCode,
} from '@/lib/types';

// Constants
const OPENAI_API_URL = 'https://api.openai.com/v1/responses';

// Error class
class DeepResearchStatusError extends Error {
  constructor(
    message: string,
    public code: DeepResearchErrorCode,
    public statusCode: number
  ) {
    super(message);
    this.name = 'DeepResearchStatusError';
  }
}

// Process API response into result format
function processApiResponse(response: DeepResearchApiResponse): DeepResearchResult {
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

  const usage = response.usage
    ? {
        inputTokens: response.usage.input_tokens,
        outputTokens: response.usage.output_tokens,
        reasoningTokens: response.usage.reasoning_tokens,
      }
    : undefined;

  return { text, citations, reasoningSteps, usage };
}

// Extract progress from API response if available
function extractProgress(response: DeepResearchApiResponse): DeepResearchProgress | undefined {
  // The API may provide progress info in different ways
  // For now, we derive it from status
  if (response.status === 'processing') {
    return {
      step: 'Researching...',
      percentage: undefined, // API doesn't always provide percentage
    };
  }
  return undefined;
}

// GET handler for job status
export async function GET(
  request: NextRequest,
  { params }: { params: Promise<{ jobId: string }> }
) {
  try {
    const { jobId } = await params;

    // Validate API key
    const apiKey = process.env.OPENAI_API_KEY;
    if (!apiKey) {
      console.error('OPENAI_API_KEY is not configured');
      return NextResponse.json(
        { error: 'Deep Research service not configured', code: 'CONFIG_ERROR' },
        { status: 500 }
      );
    }

    // Validate job ID format (basic validation)
    if (!jobId || typeof jobId !== 'string' || jobId.length === 0) {
      throw new DeepResearchStatusError(
        'Invalid job ID',
        'VALIDATION_ERROR',
        400
      );
    }

    // Fetch job status from OpenAI API
    let apiResponse: Response;
    try {
      apiResponse = await fetch(`${OPENAI_API_URL}/${jobId}`, {
        method: 'GET',
        headers: {
          'Authorization': `Bearer ${apiKey}`,
          'Content-Type': 'application/json',
        },
      });
    } catch (error) {
      throw new DeepResearchStatusError(
        `Network error: ${error instanceof Error ? error.message : 'Unknown error'}`,
        'NETWORK',
        502
      );
    }

    // Handle not found
    if (apiResponse.status === 404) {
      throw new DeepResearchStatusError(
        `Job not found: ${jobId}`,
        'JOB_NOT_FOUND',
        404
      );
    }

    // Handle forbidden (job belongs to another user)
    if (apiResponse.status === 403) {
      throw new DeepResearchStatusError(
        `Access denied to job: ${jobId}`,
        'JOB_FORBIDDEN',
        403
      );
    }

    // Handle other errors
    if (!apiResponse.ok) {
      const errorData = await apiResponse.json().catch(() => ({}));
      const message = errorData?.error?.message || 'Failed to fetch job status';
      throw new DeepResearchStatusError(
        message,
        'API_ERROR',
        apiResponse.status
      );
    }

    // Parse response
    const data = await apiResponse.json() as DeepResearchApiResponse;

    // Build status response
    const statusResponse: {
      status: DeepResearchJobStatus;
      progress?: DeepResearchProgress;
      result?: DeepResearchResult;
      error?: { code: string; message: string };
    } = {
      status: data.status as DeepResearchJobStatus,
    };

    // Add progress for in-progress jobs
    if (data.status === 'pending' || data.status === 'processing') {
      statusResponse.progress = extractProgress(data);
    }

    // Add result for completed jobs
    if (data.status === 'completed') {
      statusResponse.result = processApiResponse(data);
    }

    // Add error for failed jobs
    if (data.status === 'failed' && data.error) {
      statusResponse.error = {
        code: data.error.code,
        message: data.error.message,
      };
    }

    return NextResponse.json(statusResponse, { status: 200 });
  } catch (error) {
    console.error('[Deep Research Status] Error:', error);

    if (error instanceof DeepResearchStatusError) {
      return NextResponse.json(
        {
          error: error.message,
          code: error.code,
        },
        { status: error.statusCode }
      );
    }

    return NextResponse.json(
      { error: 'Internal server error', code: 'API_ERROR' },
      { status: 500 }
    );
  }
}
