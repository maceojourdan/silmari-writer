/**
 * SSE Client for Deep Research Streaming (REQ_011.1)
 *
 * Client-side EventSource wrapper for real-time updates
 */

import type {
  SSEEvent,
  SSEReasoningEvent,
  SSEWebSearchCallEvent,
  SSEProgressEvent,
  SSEDoneEvent,
  SSEErrorEvent,
  SSEConnectionConfig,
  SSEConnectionState,
} from './streaming-types';

// =============================================================================
// Constants
// =============================================================================

/** Default reconnection delay (REQ_011.1.7) */
export const DEFAULT_RETRY_DELAY_MS = 3000;

/** Maximum reconnection attempts */
export const DEFAULT_MAX_RETRIES = 10;

/** Event latency target (REQ_011.1.9) */
export const TARGET_LATENCY_MS = 500;

// =============================================================================
// SSE Client Class
// =============================================================================

/**
 * Event handlers for SSE events
 */
export interface SSEEventHandlers {
  onReasoning?: (event: SSEReasoningEvent) => void;
  onWebSearchCall?: (event: SSEWebSearchCallEvent) => void;
  onProgress?: (event: SSEProgressEvent) => void;
  onDone?: (event: SSEDoneEvent) => void;
  onError?: (event: SSEErrorEvent) => void;
  onConnectionStateChange?: (state: SSEConnectionState) => void;
}

/**
 * SSE Client for Deep Research streaming
 * REQ_011.1: Manages EventSource connection with auto-reconnect
 */
export class SSEClient {
  private eventSource: EventSource | null = null;
  private responseId: string;
  private retryDelayMs: number;
  private maxRetries: number;
  private retryCount: number = 0;
  private handlers: SSEEventHandlers;
  private state: SSEConnectionState;
  private reconnectTimeout: ReturnType<typeof setTimeout> | null = null;
  private isManualClose: boolean = false;

  /**
   * Create a new SSE client
   * @param config - Connection configuration
   * @param handlers - Event handlers
   */
  constructor(config: SSEConnectionConfig, handlers: SSEEventHandlers = {}) {
    this.responseId = config.responseId;
    this.retryDelayMs = config.retryDelayMs ?? DEFAULT_RETRY_DELAY_MS;
    this.maxRetries = config.maxRetries ?? DEFAULT_MAX_RETRIES;
    this.handlers = handlers;
    this.state = {
      status: 'connecting',
      retryCount: 0,
    };

    // Bind event handler if provided in config
    if (config.onEvent) {
      // Capture original handlers before reassignment to avoid recursion
      const originalReasoning = this.handlers.onReasoning;
      const originalWebSearchCall = this.handlers.onWebSearchCall;
      const originalProgress = this.handlers.onProgress;
      const originalDone = this.handlers.onDone;
      const originalError = this.handlers.onError;

      this.handlers = {
        ...this.handlers,
        onReasoning: (e) => {
          config.onEvent?.(e);
          originalReasoning?.(e);
        },
        onWebSearchCall: (e) => {
          config.onEvent?.(e);
          originalWebSearchCall?.(e);
        },
        onProgress: (e) => {
          config.onEvent?.(e);
          originalProgress?.(e);
        },
        onDone: (e) => {
          config.onEvent?.(e);
          originalDone?.(e);
        },
        onError: (e) => {
          config.onEvent?.(e);
          originalError?.(e);
        },
      };
    }

    if (config.onError) {
      const originalOnError = this.handlers.onError;
      this.handlers.onError = (e) => {
        config.onError?.(new Error(e.message));
        originalOnError?.(e);
      };
    }

    if (config.onClose) {
      const originalOnDone = this.handlers.onDone;
      this.handlers.onDone = (e) => {
        config.onClose?.();
        originalOnDone?.(e);
      };
    }
  }

  /**
   * Update connection state and notify handlers
   */
  private updateState(updates: Partial<SSEConnectionState>): void {
    this.state = { ...this.state, ...updates };
    this.handlers.onConnectionStateChange?.(this.state);
  }

  /**
   * Connect to SSE stream
   * REQ_011.1.1: Connects with response_id parameter
   */
  connect(): void {
    if (this.eventSource?.readyState === EventSource.OPEN) {
      return; // Already connected
    }

    this.isManualClose = false;
    this.updateState({ status: 'connecting' });

    const url = `/api/tools/deep-research/${this.responseId}/stream`;
    this.eventSource = new EventSource(url);

    // Handle connection open
    this.eventSource.onopen = () => {
      this.retryCount = 0;
      this.updateState({
        status: 'connected',
        retryCount: 0,
        lastEventAt: new Date().toISOString(),
        error: undefined,
      });
    };

    // Handle generic message (fallback)
    this.eventSource.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data) as SSEEvent;
        this.handleEvent(data);
      } catch (e) {
        console.warn('[SSEClient] Failed to parse message:', e);
      }
    };

    // Handle reasoning events
    // REQ_011.1.2
    this.eventSource.addEventListener('reasoning', (event: MessageEvent) => {
      this.handleTypedEvent<SSEReasoningEvent>(event, 'onReasoning');
    });

    // Handle web_search_call events
    // REQ_011.1.3
    this.eventSource.addEventListener('web_search_call', (event: MessageEvent) => {
      this.handleTypedEvent<SSEWebSearchCallEvent>(event, 'onWebSearchCall');
    });

    // Handle progress events
    // REQ_011.1.4
    this.eventSource.addEventListener('progress', (event: MessageEvent) => {
      this.handleTypedEvent<SSEProgressEvent>(event, 'onProgress');
    });

    // Handle done events
    // REQ_011.1.5
    this.eventSource.addEventListener('done', (event: MessageEvent) => {
      this.handleTypedEvent<SSEDoneEvent>(event, 'onDone');
      this.close(); // Close on completion
    });

    // Handle error events from stream
    // REQ_011.1.6
    this.eventSource.addEventListener('error', (event: MessageEvent) => {
      if (typeof event.data === 'string') {
        this.handleTypedEvent<SSEErrorEvent>(event, 'onError');
        // Close if error is not retryable
        try {
          const data = JSON.parse(event.data) as SSEErrorEvent;
          if (!data.retryable) {
            this.close();
          }
        } catch {
          // Ignore parse errors
        }
      }
    });

    // Handle connection errors
    this.eventSource.onerror = () => {
      if (this.isManualClose) {
        return; // Ignore errors during manual close
      }

      this.updateState({
        status: 'reconnecting',
        error: 'Connection error',
      });

      // Attempt reconnection
      // REQ_011.1.7: Auto-reconnect with 3s default
      this.scheduleReconnect();
    };
  }

  /**
   * Handle typed SSE event
   */
  private handleTypedEvent<T extends SSEEvent>(
    event: MessageEvent,
    handlerKey: keyof SSEEventHandlers
  ): void {
    try {
      const data = JSON.parse(event.data) as T;
      this.updateState({ lastEventAt: new Date().toISOString() });

      // Call the appropriate handler
      const handler = this.handlers[handlerKey] as ((event: T) => void) | undefined;
      handler?.(data);
    } catch (e) {
      console.warn(`[SSEClient] Failed to parse ${handlerKey} event:`, e);
    }
  }

  /**
   * Handle generic SSE event (dispatch by type)
   */
  private handleEvent(event: SSEEvent): void {
    this.updateState({ lastEventAt: new Date().toISOString() });

    switch (event.type) {
      case 'reasoning':
        this.handlers.onReasoning?.(event as SSEReasoningEvent);
        break;
      case 'web_search_call':
        this.handlers.onWebSearchCall?.(event as SSEWebSearchCallEvent);
        break;
      case 'progress':
        this.handlers.onProgress?.(event as SSEProgressEvent);
        break;
      case 'done':
        this.handlers.onDone?.(event as SSEDoneEvent);
        this.close();
        break;
      case 'error':
        this.handlers.onError?.(event as SSEErrorEvent);
        if (!(event as SSEErrorEvent).retryable) {
          this.close();
        }
        break;
    }
  }

  /**
   * Schedule reconnection attempt
   * REQ_011.1.7: 3s default retry with exponential backoff
   */
  private scheduleReconnect(): void {
    if (this.reconnectTimeout) {
      clearTimeout(this.reconnectTimeout);
    }

    if (this.retryCount >= this.maxRetries) {
      this.updateState({
        status: 'error',
        error: `Max reconnection attempts (${this.maxRetries}) exceeded`,
      });
      this.close();
      return;
    }

    // Exponential backoff: 3s, 6s, 12s, etc.
    const delay = this.retryDelayMs * Math.pow(2, this.retryCount);
    this.retryCount++;

    this.updateState({ retryCount: this.retryCount });

    this.reconnectTimeout = setTimeout(() => {
      if (!this.isManualClose) {
        this.connect();
      }
    }, delay);
  }

  /**
   * Close the SSE connection
   * REQ_011.1.10: Properly close connection
   */
  close(): void {
    this.isManualClose = true;

    if (this.reconnectTimeout) {
      clearTimeout(this.reconnectTimeout);
      this.reconnectTimeout = null;
    }

    if (this.eventSource) {
      this.eventSource.close();
      this.eventSource = null;
    }

    this.updateState({ status: 'closed' });
  }

  /**
   * Get current connection state
   */
  getState(): SSEConnectionState {
    return { ...this.state };
  }

  /**
   * Check if connected
   */
  isConnected(): boolean {
    return this.eventSource?.readyState === EventSource.OPEN;
  }

  /**
   * Get response ID
   */
  getResponseId(): string {
    return this.responseId;
  }
}

// =============================================================================
// SSE Manager for Multiple Subscribers
// =============================================================================

/**
 * Subscriber for SSE events
 */
interface SSESubscriber {
  id: string;
  handlers: SSEEventHandlers;
}

/**
 * SSE Manager for multiple concurrent subscribers
 * REQ_011.1.11: Multiple clients can subscribe to same response_id
 */
export class SSEManager {
  private clients: Map<string, SSEClient> = new Map();
  private subscribers: Map<string, SSESubscriber[]> = new Map();

  /**
   * Subscribe to SSE events for a response ID
   * Returns unsubscribe function
   */
  subscribe(
    responseId: string,
    handlers: SSEEventHandlers,
    config?: Partial<SSEConnectionConfig>
  ): () => void {
    const subscriberId = `${responseId}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

    // Get or create subscriber list
    const subs = this.subscribers.get(responseId) || [];
    subs.push({ id: subscriberId, handlers });
    this.subscribers.set(responseId, subs);

    // Get or create client
    if (!this.clients.has(responseId)) {
      const client = new SSEClient(
        {
          responseId,
          ...config,
        },
        {
          onReasoning: (e) => this.broadcast(responseId, 'onReasoning', e),
          onWebSearchCall: (e) => this.broadcast(responseId, 'onWebSearchCall', e),
          onProgress: (e) => this.broadcast(responseId, 'onProgress', e),
          onDone: (e) => {
            this.broadcast(responseId, 'onDone', e);
            this.cleanup(responseId);
          },
          onError: (e) => {
            this.broadcast(responseId, 'onError', e);
            if (!e.retryable) {
              this.cleanup(responseId);
            }
          },
          onConnectionStateChange: (s) => this.broadcast(responseId, 'onConnectionStateChange', s),
        }
      );
      this.clients.set(responseId, client);
      client.connect();
    }

    // Return unsubscribe function
    return () => {
      const subs = this.subscribers.get(responseId) || [];
      const filtered = subs.filter((s) => s.id !== subscriberId);

      if (filtered.length === 0) {
        this.subscribers.delete(responseId);
        this.cleanup(responseId);
      } else {
        this.subscribers.set(responseId, filtered);
      }
    };
  }

  /**
   * Broadcast event to all subscribers
   */
  private broadcast<K extends keyof SSEEventHandlers>(
    responseId: string,
    handlerKey: K,
    data: Parameters<NonNullable<SSEEventHandlers[K]>>[0]
  ): void {
    const subs = this.subscribers.get(responseId) || [];
    for (const sub of subs) {
      const handler = sub.handlers[handlerKey] as ((data: unknown) => void) | undefined;
      handler?.(data);
    }
  }

  /**
   * Clean up client and subscribers
   */
  private cleanup(responseId: string): void {
    const client = this.clients.get(responseId);
    if (client) {
      client.close();
      this.clients.delete(responseId);
    }
  }

  /**
   * Get all active response IDs
   */
  getActiveResponseIds(): string[] {
    return Array.from(this.clients.keys());
  }

  /**
   * Close all connections
   */
  closeAll(): void {
    for (const [responseId] of this.clients) {
      this.cleanup(responseId);
    }
    this.subscribers.clear();
  }
}

/**
 * Global SSE manager instance
 * REQ_011.1.11: Singleton for application-wide streaming management
 */
export const sseManager = new SSEManager();

// =============================================================================
// Convenience Functions
// =============================================================================

/**
 * Create and connect an SSE client
 */
export function createSSEClient(
  responseId: string,
  handlers: SSEEventHandlers,
  config?: Partial<Omit<SSEConnectionConfig, 'responseId'>>
): SSEClient {
  const client = new SSEClient({ responseId, ...config }, handlers);
  client.connect();
  return client;
}

/**
 * Subscribe to Deep Research streaming updates
 * Returns unsubscribe function
 */
export function subscribeToDeepResearch(
  responseId: string,
  handlers: SSEEventHandlers
): () => void {
  return sseManager.subscribe(responseId, handlers);
}
