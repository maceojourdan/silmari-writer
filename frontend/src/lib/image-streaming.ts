/**
 * Image Generation Streaming Module (REQ_011.2)
 *
 * Handles partial image previews during generation.
 */

import type {
  ImageStreamEvent,
  ImageStreamPartialEvent,
  ImageStreamFinalEvent,
  ImageStreamErrorEvent,
} from './streaming-types';

// =============================================================================
// Constants
// =============================================================================

/** Default number of partial previews */
export const DEFAULT_PARTIAL_IMAGES = 2;

/** Maximum partial images allowed */
export const MAX_PARTIAL_IMAGES = 3;

/** Preference storage key */
export const STREAMING_PREFERENCE_KEY = 'image_streaming_enabled';

// =============================================================================
// Types
// =============================================================================

/**
 * Image streaming configuration
 * REQ_011.2.1: API request configuration
 */
export interface ImageStreamingConfig {
  /** Enable streaming (default: true) */
  stream: boolean;
  /** Number of partial images (0-3) REQ_011.2.1 */
  partialImages: number;
  /** Request ID for tracking */
  requestId: string;
}

/**
 * Image streaming state
 */
export interface ImageStreamingState {
  /** Request ID */
  requestId: string;
  /** Streaming status */
  status: 'idle' | 'streaming' | 'completed' | 'error';
  /** Current partial image (if any) */
  currentPartial: ImageStreamPartialEvent | null;
  /** All received partials (for history) */
  receivedPartials: ImageStreamPartialEvent[];
  /** Final image (if completed) */
  finalImage: ImageStreamFinalEvent | null;
  /** Error (if failed) */
  error: ImageStreamErrorEvent | null;
  /** Start time (ms) */
  startedAt: number;
  /** Time of first partial */
  firstPartialAt?: number;
  /** Total streaming time (ms) REQ_011.2.12 */
  totalStreamingTimeMs?: number;
}

/**
 * Image streaming event handlers
 */
export interface ImageStreamingHandlers {
  /** Called when partial image received REQ_011.2.7 */
  onPartialImage?: (event: ImageStreamPartialEvent) => void;
  /** Called when final image received REQ_011.2.8 */
  onFinalImage?: (event: ImageStreamFinalEvent) => void;
  /** Called on error REQ_011.2.10 */
  onError?: (event: ImageStreamErrorEvent, partials: ImageStreamPartialEvent[]) => void;
  /** Called on streaming state change */
  onStateChange?: (state: ImageStreamingState) => void;
}

// =============================================================================
// Preference Management (REQ_011.2.9)
// =============================================================================

/**
 * Check if image streaming is enabled (user preference)
 * REQ_011.2.9: User preference toggle
 */
export function isImageStreamingEnabled(): boolean {
  if (typeof window === 'undefined' || !window.localStorage) {
    return true; // Default to enabled
  }

  const stored = window.localStorage.getItem(STREAMING_PREFERENCE_KEY);
  return stored !== 'false'; // Default to true if not set
}

/**
 * Set image streaming preference
 * REQ_011.2.9: Enable/disable toggle
 */
export function setImageStreamingEnabled(enabled: boolean): void {
  if (typeof window !== 'undefined' && window.localStorage) {
    window.localStorage.setItem(STREAMING_PREFERENCE_KEY, String(enabled));
  }
}

/**
 * Get configured number of partial images
 */
export function getPartialImagesCount(): number {
  if (!isImageStreamingEnabled()) {
    return 0;
  }
  return DEFAULT_PARTIAL_IMAGES;
}

// =============================================================================
// Image Streaming Request Builder
// =============================================================================

/**
 * Build streaming request parameters
 * REQ_011.2.1: Include stream and partial_images
 */
export function buildStreamingRequest(
  baseRequest: {
    prompt: string;
    model?: string;
    quality?: string;
    size?: string;
    [key: string]: unknown;
  },
  config: Partial<ImageStreamingConfig> = {}
): {
  request: typeof baseRequest & { stream?: boolean; partial_images?: number };
  isStreaming: boolean;
} {
  const streamingEnabled = config.stream ?? isImageStreamingEnabled();
  const partialImages = config.partialImages ?? getPartialImagesCount();

  // REQ_011.2.2: partial_images: 0 means no previews
  // REQ_011.2.3: partial_images: 1-3 for preview count
  if (!streamingEnabled || partialImages === 0) {
    return {
      request: baseRequest,
      isStreaming: false,
    };
  }

  return {
    request: {
      ...baseRequest,
      stream: true,
      partial_images: Math.min(partialImages, MAX_PARTIAL_IMAGES),
    },
    isStreaming: true,
  };
}

// =============================================================================
// Image Streaming State Management
// =============================================================================

/**
 * Create initial streaming state
 */
export function createImageStreamingState(requestId: string): ImageStreamingState {
  return {
    requestId,
    status: 'idle',
    currentPartial: null,
    receivedPartials: [],
    finalImage: null,
    error: null,
    startedAt: Date.now(),
  };
}

/**
 * Handle partial image event
 * REQ_011.2.4, REQ_011.2.7: Process partial images
 */
export function handlePartialImage(
  state: ImageStreamingState,
  event: ImageStreamPartialEvent
): ImageStreamingState {
  const now = Date.now();
  const firstPartialAt = state.firstPartialAt ?? now;

  return {
    ...state,
    status: 'streaming',
    currentPartial: event,
    receivedPartials: [...state.receivedPartials, event],
    firstPartialAt,
  };
}

/**
 * Handle final image event
 * REQ_011.2.5, REQ_011.2.8, REQ_011.2.12: Process final image
 */
export function handleFinalImage(
  state: ImageStreamingState,
  event: ImageStreamFinalEvent
): ImageStreamingState {
  const totalStreamingTimeMs = state.firstPartialAt
    ? Date.now() - state.firstPartialAt
    : Date.now() - state.startedAt;

  return {
    ...state,
    status: 'completed',
    currentPartial: null, // Clear partial
    finalImage: event,
    totalStreamingTimeMs,
  };
}

/**
 * Handle error event
 * REQ_011.2.10: Preserve partial images on error
 */
export function handleStreamingError(
  state: ImageStreamingState,
  event: ImageStreamErrorEvent
): ImageStreamingState {
  return {
    ...state,
    status: 'error',
    error: event,
    // REQ_011.2.10: Keep receivedPartials for potential display
  };
}

// =============================================================================
// Memory Management (REQ_011.2.13)
// =============================================================================

/**
 * Maximum base64 size to keep in memory (5MB)
 */
const MAX_BASE64_SIZE = 5 * 1024 * 1024;

/**
 * Check if base64 string is within safe memory limits
 * REQ_011.2.13: Memory efficiency
 */
export function isBase64Safe(base64: string): boolean {
  return base64.length <= MAX_BASE64_SIZE;
}

/**
 * Clean up partial images from memory
 * REQ_011.2.11, REQ_011.2.13: Don't persist partials, manage memory
 */
export function cleanupPartialImages(state: ImageStreamingState): ImageStreamingState {
  return {
    ...state,
    currentPartial: null,
    receivedPartials: [], // Clear partials from memory
  };
}

/**
 * Convert base64 to blob URL for display (memory efficient)
 * REQ_011.2.13: Efficient handling
 */
export function base64ToBlobUrl(base64: string, mimeType: string = 'image/png'): string {
  try {
    const byteCharacters = atob(base64);
    const byteNumbers = new Array(byteCharacters.length);
    for (let i = 0; i < byteCharacters.length; i++) {
      byteNumbers[i] = byteCharacters.charCodeAt(i);
    }
    const byteArray = new Uint8Array(byteNumbers);
    const blob = new Blob([byteArray], { type: mimeType });
    return URL.createObjectURL(blob);
  } catch {
    // Return data URL as fallback
    return `data:${mimeType};base64,${base64}`;
  }
}

/**
 * Revoke blob URL to free memory
 */
export function revokeBlobUrl(url: string): void {
  if (url.startsWith('blob:')) {
    URL.revokeObjectURL(url);
  }
}

// =============================================================================
// Image Streaming Client
// =============================================================================

/**
 * Image streaming client for handling SSE stream
 */
export class ImageStreamingClient {
  private state: ImageStreamingState;
  private handlers: ImageStreamingHandlers;
  private reader: ReadableStreamDefaultReader<Uint8Array> | null = null;
  private blobUrls: string[] = [];

  constructor(requestId: string, handlers: ImageStreamingHandlers = {}) {
    this.state = createImageStreamingState(requestId);
    this.handlers = handlers;
  }

  /**
   * Process SSE stream from fetch response
   */
  async processStream(response: Response): Promise<ImageStreamingState> {
    if (!response.body) {
      throw new Error('Response has no body');
    }

    this.reader = response.body.getReader();
    const decoder = new TextDecoder();
    let buffer = '';

    try {
      while (true) {
        const { done, value } = await this.reader.read();

        if (done) break;

        buffer += decoder.decode(value, { stream: true });

        // Process complete events
        const events = buffer.split('\n\n');
        buffer = events.pop() || ''; // Keep incomplete event in buffer

        for (const eventText of events) {
          this.processEventText(eventText);
        }
      }

      // Process any remaining buffer
      if (buffer.trim()) {
        this.processEventText(buffer);
      }

      return this.state;
    } catch (error) {
      const errorEvent: ImageStreamErrorEvent = {
        type: 'error',
        timestamp: new Date().toISOString(),
        requestId: this.state.requestId,
        code: 'STREAM_ERROR',
        message: error instanceof Error ? error.message : 'Unknown error',
        partialImagesGenerated: this.state.receivedPartials.length,
      };

      this.state = handleStreamingError(this.state, errorEvent);
      this.handlers.onError?.(errorEvent, this.state.receivedPartials);
      this.handlers.onStateChange?.(this.state);

      return this.state;
    }
  }

  /**
   * Process a single SSE event text
   */
  private processEventText(eventText: string): void {
    const lines = eventText.split('\n');
    let eventData = '';

    for (const line of lines) {
      if (line.startsWith('data:')) {
        eventData = line.slice(5).trim();
      }
    }

    if (!eventData) return;

    try {
      const event = JSON.parse(eventData) as ImageStreamEvent;
      this.handleEvent(event);
    } catch {
      console.warn('[ImageStreamingClient] Failed to parse event:', eventData);
    }
  }

  /**
   * Handle parsed event
   */
  private handleEvent(event: ImageStreamEvent): void {
    switch (event.type) {
      case 'partial_image':
        this.state = handlePartialImage(this.state, event);
        this.handlers.onPartialImage?.(event);
        break;

      case 'final_image':
        this.state = handleFinalImage(this.state, event);
        this.handlers.onFinalImage?.(event);
        // Cleanup partials after final
        this.state = cleanupPartialImages(this.state);
        break;

      case 'error':
        this.state = handleStreamingError(this.state, event);
        this.handlers.onError?.(event, this.state.receivedPartials);
        break;
    }

    this.handlers.onStateChange?.(this.state);
  }

  /**
   * Cancel streaming
   */
  async cancel(): Promise<void> {
    if (this.reader) {
      await this.reader.cancel();
      this.reader = null;
    }
    this.cleanup();
  }

  /**
   * Cleanup resources
   */
  cleanup(): void {
    // Revoke all blob URLs
    for (const url of this.blobUrls) {
      revokeBlobUrl(url);
    }
    this.blobUrls = [];
  }

  /**
   * Get current state
   */
  getState(): ImageStreamingState {
    return { ...this.state };
  }
}

// =============================================================================
// Convenience Functions
// =============================================================================

/**
 * Create image streaming client and process response
 */
export async function streamImageGeneration(
  response: Response,
  handlers: ImageStreamingHandlers
): Promise<ImageStreamingState> {
  const requestId = `img_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  const client = new ImageStreamingClient(requestId, handlers);

  try {
    return await client.processStream(response);
  } finally {
    client.cleanup();
  }
}

/**
 * Format streaming time for display
 * REQ_011.2.12: Display total streaming time
 */
export function formatStreamingTime(ms: number): string {
  if (ms < 1000) {
    return `${ms}ms`;
  }
  return `${(ms / 1000).toFixed(1)}s`;
}
