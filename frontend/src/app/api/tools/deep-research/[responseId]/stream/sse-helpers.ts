// SSE streaming helper utilities shared by route and tests.

export const KEEP_ALIVE_INTERVAL_MS = 15000; // 15 seconds
export const POLL_INTERVAL_MS = 2000; // 2 seconds between polls
export const MAX_POLL_DURATION_MS = 1800000; // 30 minutes max
export const OPENAI_API_URL = 'https://api.openai.com/v1/responses';

export type SSEEventType = 'reasoning' | 'web_search_call' | 'progress' | 'done' | 'error';

export interface SSEEventData {
  type: SSEEventType;
  timestamp: string;
  responseId: string;
  [key: string]: unknown;
}

/**
 * Format SSE event for streaming
 * REQ_011.1.12: JSON-encoded events
 */
export function formatSSEEvent(event: string, data: SSEEventData): string {
  return `event: ${event}\ndata: ${JSON.stringify(data)}\n\n`;
}

/**
 * Format SSE comment for keep-alive
 * REQ_011.1.8: Keep-alive comments
 */
export function formatSSEComment(comment: string): string {
  return `: ${comment}\n\n`;
}

/**
 * Map OpenAI response status to progress percentage
 */
export function estimateProgress(
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
export function inferStepType(text: string): 'planning' | 'searching' | 'synthesizing' {
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
