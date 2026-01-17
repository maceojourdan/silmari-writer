import { NextRequest } from 'next/server';

// =============================================================================
// REQ_011.1: SSE Streaming Route for Deep Research
// =============================================================================

// Constants
const KEEP_ALIVE_INTERVAL_MS = 15000; // 15 seconds
const POLL_INTERVAL_MS = 2000; // 2 seconds between polls
const MAX_POLL_DURATION_MS = 1800000; // 30 minutes max
const OPENAI_API_URL = 'https://api.openai.com/v1/responses';

// Event types for SSE
type SSEEventType = 'reasoning' | 'web_search_call' | 'progress' | 'done' | 'error';

interface SSEEventData {
  type: SSEEventType;
  timestamp: string;
  responseId: string;
  [key: string]: unknown;
}

/**
 * Format SSE event for streaming
 * REQ_011.1.12: JSON-encoded events
 */
function formatSSEEvent(event: string, data: SSEEventData): string {
  return `event: ${event}\ndata: ${JSON.stringify(data)}\n\n`;
}

/**
 * Format SSE comment for keep-alive
 * REQ_011.1.8: Keep-alive comments
 */
function formatSSEComment(comment: string): string {
  return `: ${comment}\n\n`;
}

/**
 * Map OpenAI response status to progress percentage
 */
function estimateProgress(
  status: string,
  elapsedMs: number,
  hasReasoningSteps: boolean,
  hasSearchResults: boolean
): number {
  // Return 100 for completed status
  if (status === 'completed') {
    return 100;
  }

  // Base progress from status
  let progress = 0;

  if (status === 'pending') {
    progress = Math.min(10, Math.floor(elapsedMs / 10000) * 5); // 5% per 10s, max 10%
  } else if (status === 'processing') {
    progress = 10;

    // Add progress based on intermediate results
    if (hasReasoningSteps) progress += 20;
    if (hasSearchResults) progress += 30;

    // Time-based progress (estimate based on typical duration)
    const timeProgress = Math.min(30, Math.floor(elapsedMs / 60000) * 10); // 10% per minute, max 30%
    progress += timeProgress;
  }

  return Math.min(progress, 95); // Cap at 95% until complete
}

/**
 * Determine reasoning step type from content
 */
function inferStepType(text: string): 'planning' | 'searching' | 'synthesizing' {
  const lower = text.toLowerCase();
  // Check synthesizing first (more specific patterns)
  if (lower.includes('synthesiz') || lower.includes('combin') || lower.includes('summariz') || lower.includes('report')) {
    return 'synthesizing';
  }
  // Then check for searching patterns
  if (lower.includes('search') || lower.includes('looking for') || lower.includes('finding')) {
    return 'searching';
  }
  return 'planning';
}

/**
 * GET handler for SSE streaming
 * REQ_011.1.1: Accepts response_id parameter
 */
export async function GET(
  request: NextRequest,
  { params }: { params: Promise<{ responseId: string }> }
) {
  const { responseId } = await params;

  // Validate API key
  const apiKey = process.env.OPENAI_API_KEY;
  if (!apiKey) {
    return new Response(
      JSON.stringify({ error: 'API key not configured', code: 'CONFIG_ERROR' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    );
  }

  // Validate response ID format
  if (!responseId || !/^resp_[a-zA-Z0-9]+$/.test(responseId)) {
    return new Response(
      JSON.stringify({ error: 'Invalid response ID format', code: 'VALIDATION_ERROR' }),
      { status: 400, headers: { 'Content-Type': 'application/json' } }
    );
  }

  // Track state for deduplication
  const lastSeenReasoningIds = new Set<string>();
  const lastSeenSearchIds = new Set<string>();
  let lastProgress = 0;
  const startTime = Date.now();

  // Create readable stream
  const stream = new ReadableStream({
    async start(controller) {
      const encoder = new TextEncoder();
      let keepAliveInterval: NodeJS.Timeout | null = null;
      let isCompleted = false;

      // Send keep-alive comments
      // REQ_011.1.8: Every 15 seconds
      keepAliveInterval = setInterval(() => {
        if (!isCompleted) {
          controller.enqueue(encoder.encode(formatSSEComment(`keep-alive ${Date.now()}`)));
        }
      }, KEEP_ALIVE_INTERVAL_MS);

      // Helper to send event
      const sendEvent = (type: SSEEventType, data: Omit<SSEEventData, 'type' | 'timestamp' | 'responseId'>) => {
        const event: SSEEventData = {
          type,
          timestamp: new Date().toISOString(),
          responseId,
          ...data,
        };
        controller.enqueue(encoder.encode(formatSSEEvent(type, event)));
      };

      // Cleanup function
      const cleanup = () => {
        isCompleted = true;
        if (keepAliveInterval) {
          clearInterval(keepAliveInterval);
          keepAliveInterval = null;
        }
      };

      try {
        // Poll loop
        while (!isCompleted) {
          const elapsedMs = Date.now() - startTime;

          // Check timeout
          // REQ_011.1.10: Close on timeout
          if (elapsedMs > MAX_POLL_DURATION_MS) {
            sendEvent('error', {
              code: 'TIMEOUT',
              message: 'Operation timed out after 30 minutes',
              retryable: false,
            });
            cleanup();
            controller.close();
            return;
          }

          // Fetch status from OpenAI
          const response = await fetch(`${OPENAI_API_URL}/${responseId}`, {
            method: 'GET',
            headers: {
              'Authorization': `Bearer ${apiKey}`,
              'Content-Type': 'application/json',
            },
          });

          if (!response.ok) {
            const errorText = await response.text();
            let errorData: { error?: { message?: string; code?: string } } = {};
            try {
              errorData = JSON.parse(errorText);
            } catch {
              // Not JSON
            }

            // Handle specific errors
            if (response.status === 404) {
              sendEvent('error', {
                code: 'JOB_NOT_FOUND',
                message: 'Research job not found',
                retryable: false,
              });
            } else if (response.status === 429) {
              sendEvent('error', {
                code: 'RATE_LIMIT',
                message: 'Rate limit exceeded',
                retryable: true,
              });
            } else {
              sendEvent('error', {
                code: 'API_ERROR',
                message: errorData.error?.message || `API error: ${response.status}`,
                retryable: response.status >= 500,
              });
            }

            cleanup();
            controller.close();
            return;
          }

          const data = await response.json();

          // Process reasoning steps
          // REQ_011.1.2: Send reasoning events
          if (data.output) {
            for (const item of data.output) {
              // Handle reasoning items
              if (item.type === 'reasoning' && item.id && !lastSeenReasoningIds.has(item.id)) {
                lastSeenReasoningIds.add(item.id);

                const summaryText = item.summary
                  ?.filter((s: { type: string }) => s.type === 'summary_text')
                  ?.map((s: { text: string }) => s.text)
                  ?.join(' ') || '';

                if (summaryText) {
                  sendEvent('reasoning', {
                    stepIndex: lastSeenReasoningIds.size - 1,
                    stepType: inferStepType(summaryText),
                    summary: summaryText,
                  });
                }
              }

              // Handle web search calls
              // REQ_011.1.3: Send web_search_call events
              if (item.type === 'web_search_call' && item.id && !lastSeenSearchIds.has(item.id)) {
                lastSeenSearchIds.add(item.id);

                sendEvent('web_search_call', {
                  query: item.query || '',
                  searchId: item.id,
                });
              }
            }
          }

          // Send progress update
          // REQ_011.1.4: Progress percentage
          const progress = estimateProgress(
            data.status,
            elapsedMs,
            lastSeenReasoningIds.size > 0,
            lastSeenSearchIds.size > 0
          );

          if (progress > lastProgress) {
            lastProgress = progress;
            sendEvent('progress', {
              percentage: progress,
              elapsedMs,
              currentPhase: lastSeenSearchIds.size > 0 ? 'searching' :
                          lastSeenReasoningIds.size > 0 ? 'planning' : 'planning',
            });
          }

          // Check for completion
          // REQ_011.1.5: Send done event
          if (data.status === 'completed') {
            sendEvent('done', {
              finalReportAvailable: true,
              totalElapsedMs: elapsedMs,
              resultId: data.id,
            });
            cleanup();
            controller.close();
            return;
          }

          // Check for failure
          // REQ_011.1.6: Send error event
          if (data.status === 'failed') {
            sendEvent('error', {
              code: data.error?.code || 'API_ERROR',
              message: data.error?.message || 'Research job failed',
              retryable: false,
            });
            cleanup();
            controller.close();
            return;
          }

          // Wait before next poll
          await new Promise(resolve => setTimeout(resolve, POLL_INTERVAL_MS));
        }
      } catch (error) {
        // Handle unexpected errors
        const message = error instanceof Error ? error.message : 'Unknown error';
        sendEvent('error', {
          code: 'NETWORK',
          message: `Stream error: ${message}`,
          retryable: true,
        });
        cleanup();
        controller.close();
      }
    },
  });

  // Return SSE response
  // REQ_011.1: SSE headers
  return new Response(stream, {
    headers: {
      'Content-Type': 'text/event-stream',
      'Cache-Control': 'no-cache',
      'Connection': 'keep-alive',
      'X-Accel-Buffering': 'no', // Disable nginx buffering
    },
  });
}

// Export constants and helpers for testing
export {
  KEEP_ALIVE_INTERVAL_MS,
  POLL_INTERVAL_MS,
  MAX_POLL_DURATION_MS,
  OPENAI_API_URL,
  formatSSEEvent,
  formatSSEComment,
  estimateProgress,
  inferStepType,
};
export type { SSEEventType, SSEEventData };
