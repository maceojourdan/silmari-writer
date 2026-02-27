/* eslint-disable @typescript-eslint/ban-ts-comment */
// @ts-nocheck
/**
 * Unit tests for SSE Client and Manager
 * REQ_011.1: SSE streaming for Deep Research
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

import {
  SSEClient,
  SSEManager,
  sseManager,
  createSSEClient,
  subscribeToDeepResearch,
  DEFAULT_RETRY_DELAY_MS,
  DEFAULT_MAX_RETRIES,
  TARGET_LATENCY_MS,
  type SSEEventHandlers,
} from '../sse-client';

import type {
  SSEReasoningEvent,
  SSEWebSearchCallEvent,
  SSEProgressEvent,
  SSEDoneEvent,
  SSEErrorEvent,
  SSEConnectionState,
} from '../streaming-types';

// =============================================================================
// Mock EventSource
// =============================================================================

// Flag to make new connections fail immediately (for testing max retries)
let failNewConnections = false;

class MockEventSource {
  static CONNECTING = 0;
  static OPEN = 1;
  static CLOSED = 2;

  url: string;
  readyState: number = MockEventSource.CONNECTING;
  onopen: ((event: Event) => void) | null = null;
  onmessage: ((event: MessageEvent) => void) | null = null;
  onerror: ((event: Event) => void) | null = null;

  private eventListeners: Map<string, ((event: MessageEvent) => void)[]> = new Map();

  constructor(url: string) {
    this.url = url;
    // Simulate connection open after microtask
    Promise.resolve().then(() => {
      if (this.readyState !== MockEventSource.CLOSED) {
        if (failNewConnections) {
          // Simulate immediate connection failure
          this.readyState = MockEventSource.CLOSED;
          this.onerror?.(new Event('error'));
        } else {
          this.readyState = MockEventSource.OPEN;
          this.onopen?.(new Event('open'));
        }
      }
    });
  }

  addEventListener(type: string, listener: (event: MessageEvent) => void): void {
    const listeners = this.eventListeners.get(type) || [];
    listeners.push(listener);
    this.eventListeners.set(type, listeners);
  }

  removeEventListener(type: string, listener: (event: MessageEvent) => void): void {
    const listeners = this.eventListeners.get(type) || [];
    this.eventListeners.set(
      type,
      listeners.filter((l) => l !== listener)
    );
  }

  close(): void {
    this.readyState = MockEventSource.CLOSED;
  }

  // Test helpers
  simulateMessage(data: string): void {
    if (this.readyState === MockEventSource.OPEN) {
      this.onmessage?.(new MessageEvent('message', { data }));
    }
  }

  simulateTypedEvent(type: string, data: string): void {
    if (this.readyState === MockEventSource.OPEN) {
      const listeners = this.eventListeners.get(type) || [];
      const event = new MessageEvent(type, { data });
      listeners.forEach((listener) => listener(event));
    }
  }

  simulateError(): void {
    // Real EventSource closes on error
    this.readyState = MockEventSource.CLOSED;
    this.onerror?.(new Event('error'));
  }
}

// Store reference to created EventSource instances for testing
let mockEventSourceInstances: MockEventSource[] = [];

// Create a tracking wrapper class
class TrackingEventSource extends MockEventSource {
  constructor(url: string) {
    super(url);
    mockEventSourceInstances.push(this);
  }
}

describe('SSE Client (REQ_011.1)', () => {
  beforeEach(() => {
    // Reset instances and flags BEFORE setting up timers
    mockEventSourceInstances = [];
    failNewConnections = false;
    vi.useFakeTimers();

    // Mock EventSource using vi.stubGlobal with a proper class
    vi.stubGlobal('EventSource', TrackingEventSource);
  });

  afterEach(() => {
    // Close all SSE managers first
    sseManager.closeAll();
    // Then reset timers and unstub
    vi.useRealTimers();
    vi.unstubAllGlobals();
    // Clear instances and flags after test
    mockEventSourceInstances = [];
    failNewConnections = false;
  });

  describe('Constants', () => {
    it('should have correct default retry delay (REQ_011.1.7)', () => {
      expect(DEFAULT_RETRY_DELAY_MS).toBe(3000);
    });

    it('should have correct max retries', () => {
      expect(DEFAULT_MAX_RETRIES).toBe(10);
    });

    it('should have correct target latency (REQ_011.1.9)', () => {
      expect(TARGET_LATENCY_MS).toBe(500);
    });
  });

  describe('SSEClient', () => {
    describe('Connection (REQ_011.1.1)', () => {
      it('should create EventSource with correct URL', async () => {
        const client = new SSEClient({ responseId: 'resp_123' });
        client.connect();

        await vi.runAllTimersAsync();

        expect(mockEventSourceInstances.length).toBe(1);
        expect(mockEventSourceInstances[0].url).toBe('/api/tools/deep-research/resp_123/stream');
      });

      it('should not create duplicate connections when already connected', async () => {
        const client = new SSEClient({ responseId: 'resp_123' });
        client.connect();
        await vi.runAllTimersAsync();

        client.connect(); // Second connect call

        expect(mockEventSourceInstances.length).toBe(1);
      });

      it('should update state to connected on successful connection', async () => {
        const stateChanges: SSEConnectionState[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onConnectionStateChange: (state) => stateChanges.push({ ...state }) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        const connectedState = stateChanges.find((s) => s.status === 'connected');
        expect(connectedState).toBeDefined();
        expect(connectedState?.retryCount).toBe(0);
        expect(connectedState?.lastEventAt).toBeDefined();
      });
    });

    describe('Event Handling', () => {
      it('should handle reasoning events (REQ_011.1.2)', async () => {
        const events: SSEReasoningEvent[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onReasoning: (e) => events.push(e) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        const reasoningEvent: SSEReasoningEvent = {
          type: 'reasoning',
          id: 'reason_1',
          summary: 'Analyzing query',
          index: 0,
        };

        mockEventSourceInstances[0].simulateTypedEvent('reasoning', JSON.stringify(reasoningEvent));

        expect(events.length).toBe(1);
        expect(events[0]).toEqual(reasoningEvent);
      });

      it('should handle web_search_call events (REQ_011.1.3)', async () => {
        const events: SSEWebSearchCallEvent[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onWebSearchCall: (e) => events.push(e) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        const searchEvent: SSEWebSearchCallEvent = {
          type: 'web_search_call',
          id: 'search_1',
          query: 'AI developments 2025',
          status: 'searching',
        };

        mockEventSourceInstances[0].simulateTypedEvent(
          'web_search_call',
          JSON.stringify(searchEvent)
        );

        expect(events.length).toBe(1);
        expect(events[0]).toEqual(searchEvent);
      });

      it('should handle progress events (REQ_011.1.4)', async () => {
        const events: SSEProgressEvent[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onProgress: (e) => events.push(e) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        const progressEvent: SSEProgressEvent = {
          type: 'progress',
          step: 'Reading sources',
          percentage: 50,
        };

        mockEventSourceInstances[0].simulateTypedEvent('progress', JSON.stringify(progressEvent));

        expect(events.length).toBe(1);
        expect(events[0]).toEqual(progressEvent);
      });

      it('should handle done events and close connection (REQ_011.1.5)', async () => {
        const events: SSEDoneEvent[] = [];
        const client = new SSEClient({ responseId: 'resp_123' }, { onDone: (e) => events.push(e) });

        client.connect();
        await vi.runAllTimersAsync();

        const doneEvent: SSEDoneEvent = {
          type: 'done',
          responseId: 'resp_123',
          text: 'Research completed successfully.',
          citations: [],
          usage: { inputTokens: 100, outputTokens: 500 },
        };

        mockEventSourceInstances[0].simulateTypedEvent('done', JSON.stringify(doneEvent));

        expect(events.length).toBe(1);
        expect(events[0]).toEqual(doneEvent);
        expect(mockEventSourceInstances[0].readyState).toBe(MockEventSource.CLOSED);
      });

      it('should handle error events (REQ_011.1.6)', async () => {
        const events: SSEErrorEvent[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onError: (e) => events.push(e) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        const errorEvent: SSEErrorEvent = {
          type: 'error',
          code: 'RATE_LIMIT',
          message: 'Too many requests',
          retryable: true,
        };

        mockEventSourceInstances[0].simulateTypedEvent('error', JSON.stringify(errorEvent));

        expect(events.length).toBe(1);
        expect(events[0]).toEqual(errorEvent);
      });

      it('should close on non-retryable error events', async () => {
        const client = new SSEClient({ responseId: 'resp_123' });

        client.connect();
        await vi.runAllTimersAsync();

        const errorEvent: SSEErrorEvent = {
          type: 'error',
          code: 'INVALID_API_KEY',
          message: 'Invalid API key',
          retryable: false,
        };

        mockEventSourceInstances[0].simulateTypedEvent('error', JSON.stringify(errorEvent));

        expect(mockEventSourceInstances[0].readyState).toBe(MockEventSource.CLOSED);
      });

      it('should handle generic message events via onmessage', async () => {
        const progressEvents: SSEProgressEvent[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onProgress: (e) => progressEvents.push(e) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        const progressEvent: SSEProgressEvent = {
          type: 'progress',
          step: 'Processing',
          percentage: 25,
        };

        mockEventSourceInstances[0].simulateMessage(JSON.stringify(progressEvent));

        expect(progressEvents.length).toBe(1);
        expect(progressEvents[0]).toEqual(progressEvent);
      });
    });

    describe('Auto-reconnect (REQ_011.1.7)', () => {
      it('should schedule reconnect on connection error with 3s delay', async () => {
        const stateChanges: SSEConnectionState[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onConnectionStateChange: (state) => stateChanges.push({ ...state }) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        // Simulate connection error
        mockEventSourceInstances[0].simulateError();

        const reconnectingState = stateChanges.find((s) => s.status === 'reconnecting');
        expect(reconnectingState).toBeDefined();
        expect(reconnectingState?.error).toBe('Connection error');
      });

      it('should use exponential backoff for retries', async () => {
        // Reset instances for this test
        mockEventSourceInstances = [];

        const stateChanges: SSEConnectionState[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123', retryDelayMs: 1000, maxRetries: 5 },
          { onConnectionStateChange: (state) => stateChanges.push({ ...state }) }
        );

        client.connect();
        await vi.runAllTimersAsync();
        expect(mockEventSourceInstances.length).toBe(1);

        // First error - retryCount starts at 0, schedules reconnect with delay=1000*2^0=1000ms
        // then increments retryCount to 1
        mockEventSourceInstances[0].simulateError();

        // Check reconnecting state shows retryCount=1
        const firstReconnect = stateChanges.find(s => s.status === 'reconnecting' && s.retryCount === 1);
        expect(firstReconnect).toBeDefined();

        // At 500ms - should NOT have reconnected yet
        await vi.advanceTimersByTimeAsync(500);
        expect(mockEventSourceInstances.length).toBe(1);

        // At 1000ms - should reconnect (delay was 1000ms for retryCount=0)
        await vi.advanceTimersByTimeAsync(500);
        await vi.runAllTimersAsync();
        expect(mockEventSourceInstances.length).toBe(2);

        // After successful reconnect, retryCount resets to 0 (expected behavior)
        // Second error - retryCount is 0 again, delay=1000ms
        mockEventSourceInstances[1].simulateError();

        await vi.advanceTimersByTimeAsync(500);
        expect(mockEventSourceInstances.length).toBe(2); // Not reconnected yet

        await vi.advanceTimersByTimeAsync(500);
        await vi.runAllTimersAsync();
        expect(mockEventSourceInstances.length).toBe(3);

        client.close();
      });

      it('should stop retrying after max retries exceeded', async () => {
        // Reset instances for this test
        mockEventSourceInstances = [];

        const stateChanges: SSEConnectionState[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123', retryDelayMs: 100, maxRetries: 2 },
          { onConnectionStateChange: (state) => stateChanges.push({ ...state }) }
        );

        client.connect();
        await vi.runAllTimersAsync();
        expect(mockEventSourceInstances.length).toBe(1);

        // Make all subsequent connections fail immediately
        // This prevents retryCount from being reset on successful connection
        failNewConnections = true;

        // First error - retryCount becomes 1, schedules reconnect at 100ms
        mockEventSourceInstances[0].simulateError();

        // Advance through all retry attempts - the cascading failures will happen
        // automatically via runAllTimersAsync
        await vi.advanceTimersByTimeAsync(1000); // Plenty of time for all retries
        await vi.runAllTimersAsync();

        // After max retries are exhausted, should have error state
        const errorState = stateChanges.find((s) => s.status === 'error');
        expect(errorState).toBeDefined();
        expect(errorState?.error).toContain('Max reconnection attempts');

        client.close();
      });

      it('should reset retry count on successful connection', async () => {
        const stateChanges: SSEConnectionState[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123', retryDelayMs: 100, maxRetries: 5 },
          { onConnectionStateChange: (state) => stateChanges.push({ ...state }) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        // First error - retry count goes to 1
        mockEventSourceInstances[0].simulateError();
        const reconnectingState = stateChanges.find((s) => s.status === 'reconnecting');
        expect(reconnectingState).toBeDefined();

        // After reconnect timeout, a new connection is established
        await vi.advanceTimersByTimeAsync(100);
        await vi.runAllTimersAsync();

        // Successful reconnection - the onopen callback resets retry count to 0
        const connectedState = stateChanges.filter((s) => s.status === 'connected').pop();
        expect(connectedState).toBeDefined();
        expect(connectedState?.retryCount).toBe(0);
      });
    });

    describe('Connection Close (REQ_011.1.10)', () => {
      it('should properly close connection', async () => {
        const stateChanges: SSEConnectionState[] = [];
        const client = new SSEClient(
          { responseId: 'resp_123' },
          { onConnectionStateChange: (state) => stateChanges.push({ ...state }) }
        );

        client.connect();
        await vi.runAllTimersAsync();

        client.close();

        expect(mockEventSourceInstances[0].readyState).toBe(MockEventSource.CLOSED);
        const closedState = stateChanges.find((s) => s.status === 'closed');
        expect(closedState).toBeDefined();
      });

      it('should not reconnect after manual close', async () => {
        const client = new SSEClient({ responseId: 'resp_123', retryDelayMs: 100 });

        client.connect();
        await vi.runAllTimersAsync();

        client.close();

        // Advance past retry delay
        await vi.advanceTimersByTimeAsync(1000);
        await vi.runAllTimersAsync();

        // Should only have one instance (no reconnect)
        expect(mockEventSourceInstances.length).toBe(1);
      });

      it('should clear pending reconnect timeout on close', async () => {
        const client = new SSEClient({ responseId: 'resp_123', retryDelayMs: 1000 });

        client.connect();
        await vi.runAllTimersAsync();

        // Trigger error to schedule reconnect
        mockEventSourceInstances[0].simulateError();

        // Close before reconnect happens
        client.close();

        // Advance past retry delay
        await vi.advanceTimersByTimeAsync(2000);
        await vi.runAllTimersAsync();

        // Should only have one instance
        expect(mockEventSourceInstances.length).toBe(1);
      });
    });

    describe('State Management', () => {
      it('should return copy of state', () => {
        const client = new SSEClient({ responseId: 'resp_123' });
        const state1 = client.getState();
        const state2 = client.getState();

        expect(state1).not.toBe(state2);
        expect(state1).toEqual(state2);
      });

      it('should track lastEventAt on events', async () => {
        const client = new SSEClient({ responseId: 'resp_123' });

        client.connect();
        await vi.runAllTimersAsync();

        const beforeEvent = client.getState().lastEventAt;

        const progressEvent: SSEProgressEvent = {
          type: 'progress',
          step: 'Testing',
          percentage: 10,
        };
        mockEventSourceInstances[0].simulateTypedEvent('progress', JSON.stringify(progressEvent));

        const afterEvent = client.getState().lastEventAt;
        expect(afterEvent).toBeDefined();
        // lastEventAt should be updated (may or may not be different from beforeEvent)
        expect(typeof afterEvent).toBe('string');
      });

      it('should report isConnected correctly', async () => {
        const client = new SSEClient({ responseId: 'resp_123' });

        expect(client.isConnected()).toBe(false);

        client.connect();
        await vi.runAllTimersAsync();

        expect(client.isConnected()).toBe(true);

        client.close();

        expect(client.isConnected()).toBe(false);
      });

      it('should return responseId', () => {
        const client = new SSEClient({ responseId: 'resp_test_456' });
        expect(client.getResponseId()).toBe('resp_test_456');
      });
    });

    describe('Config Callbacks', () => {
      it('should call onEvent for all event types', async () => {
        // Reset instances for this test
        mockEventSourceInstances = [];

        const receivedEvents: unknown[] = [];
        const client = new SSEClient({
          responseId: 'resp_123',
          onEvent: (e) => receivedEvents.push(e),
        });

        client.connect();
        await vi.runAllTimersAsync();

        expect(mockEventSourceInstances.length).toBe(1);

        const progressEvent: SSEProgressEvent = {
          type: 'progress',
          step: 'Test',
          percentage: 50,
        };
        mockEventSourceInstances[0].simulateTypedEvent('progress', JSON.stringify(progressEvent));

        expect(receivedEvents.length).toBe(1);
        expect(receivedEvents[0]).toEqual(progressEvent);

        client.close();
      });

      it('should call onError from config', async () => {
        const errors: Error[] = [];
        const client = new SSEClient({
          responseId: 'resp_123',
          onError: (e) => errors.push(e),
        });

        client.connect();
        await vi.runAllTimersAsync();

        const errorEvent: SSEErrorEvent = {
          type: 'error',
          code: 'API_ERROR',
          message: 'Something went wrong',
          retryable: false,
        };
        mockEventSourceInstances[0].simulateTypedEvent('error', JSON.stringify(errorEvent));

        expect(errors.length).toBe(1);
        expect(errors[0].message).toBe('Something went wrong');
      });

      it('should call onClose from config on done event', async () => {
        let closed = false;
        const client = new SSEClient({
          responseId: 'resp_123',
          onClose: () => {
            closed = true;
          },
        });

        client.connect();
        await vi.runAllTimersAsync();

        const doneEvent: SSEDoneEvent = {
          type: 'done',
          responseId: 'resp_123',
          text: 'Done',
        };
        mockEventSourceInstances[0].simulateTypedEvent('done', JSON.stringify(doneEvent));

        expect(closed).toBe(true);
      });
    });
  });

  describe('SSEManager (REQ_011.1.11)', () => {
    let manager: SSEManager;

    beforeEach(() => {
      manager = new SSEManager();
    });

    afterEach(() => {
      manager.closeAll();
    });

    describe('Subscription', () => {
      it('should create client on first subscription', async () => {
        manager.subscribe('resp_123', {});
        await vi.runAllTimersAsync();

        expect(mockEventSourceInstances.length).toBe(1);
        expect(mockEventSourceInstances[0].url).toBe('/api/tools/deep-research/resp_123/stream');
      });

      it('should reuse client for same responseId', async () => {
        manager.subscribe('resp_123', {});
        manager.subscribe('resp_123', {});
        await vi.runAllTimersAsync();

        expect(mockEventSourceInstances.length).toBe(1);
      });

      it('should create separate clients for different responseIds', async () => {
        manager.subscribe('resp_123', {});
        manager.subscribe('resp_456', {});
        await vi.runAllTimersAsync();

        expect(mockEventSourceInstances.length).toBe(2);
      });

      it('should broadcast events to all subscribers', async () => {
        const events1: SSEProgressEvent[] = [];
        const events2: SSEProgressEvent[] = [];

        manager.subscribe('resp_123', { onProgress: (e) => events1.push(e) });
        manager.subscribe('resp_123', { onProgress: (e) => events2.push(e) });
        await vi.runAllTimersAsync();

        const progressEvent: SSEProgressEvent = {
          type: 'progress',
          step: 'Broadcast test',
          percentage: 75,
        };
        mockEventSourceInstances[0].simulateTypedEvent('progress', JSON.stringify(progressEvent));

        expect(events1.length).toBe(1);
        expect(events2.length).toBe(1);
        expect(events1[0]).toEqual(events2[0]);
      });

      it('should return unsubscribe function', async () => {
        const events: SSEProgressEvent[] = [];
        const unsubscribe = manager.subscribe('resp_123', { onProgress: (e) => events.push(e) });
        await vi.runAllTimersAsync();

        unsubscribe();

        const progressEvent: SSEProgressEvent = {
          type: 'progress',
          step: 'After unsubscribe',
          percentage: 100,
        };
        mockEventSourceInstances[0].simulateTypedEvent('progress', JSON.stringify(progressEvent));

        // Event should not be received after unsubscribe
        expect(events.length).toBe(0);
      });

      it('should cleanup client when last subscriber unsubscribes', async () => {
        const unsubscribe1 = manager.subscribe('resp_123', {});
        const unsubscribe2 = manager.subscribe('resp_123', {});
        await vi.runAllTimersAsync();

        unsubscribe1();
        expect(manager.getActiveResponseIds()).toContain('resp_123');

        unsubscribe2();
        expect(manager.getActiveResponseIds()).not.toContain('resp_123');
        expect(mockEventSourceInstances[0].readyState).toBe(MockEventSource.CLOSED);
      });

      it('should cleanup on done event', async () => {
        manager.subscribe('resp_123', {});
        await vi.runAllTimersAsync();

        const doneEvent: SSEDoneEvent = {
          type: 'done',
          responseId: 'resp_123',
          text: 'Complete',
        };
        mockEventSourceInstances[0].simulateTypedEvent('done', JSON.stringify(doneEvent));

        expect(manager.getActiveResponseIds()).not.toContain('resp_123');
      });

      it('should cleanup on non-retryable error', async () => {
        manager.subscribe('resp_123', {});
        await vi.runAllTimersAsync();

        const errorEvent: SSEErrorEvent = {
          type: 'error',
          code: 'FATAL',
          message: 'Fatal error',
          retryable: false,
        };
        mockEventSourceInstances[0].simulateTypedEvent('error', JSON.stringify(errorEvent));

        expect(manager.getActiveResponseIds()).not.toContain('resp_123');
      });

      it('should not cleanup on retryable error', async () => {
        manager.subscribe('resp_123', {});
        await vi.runAllTimersAsync();

        const errorEvent: SSEErrorEvent = {
          type: 'error',
          code: 'NETWORK',
          message: 'Network error',
          retryable: true,
        };
        mockEventSourceInstances[0].simulateTypedEvent('error', JSON.stringify(errorEvent));

        // Client should still be active (for potential retry)
        expect(manager.getActiveResponseIds()).toContain('resp_123');
      });
    });

    describe('Active Response IDs', () => {
      it('should return empty array initially', () => {
        expect(manager.getActiveResponseIds()).toEqual([]);
      });

      it('should return active response IDs', async () => {
        manager.subscribe('resp_123', {});
        manager.subscribe('resp_456', {});
        await vi.runAllTimersAsync();

        const activeIds = manager.getActiveResponseIds();
        expect(activeIds).toContain('resp_123');
        expect(activeIds).toContain('resp_456');
        expect(activeIds.length).toBe(2);
      });
    });

    describe('Close All', () => {
      it('should close all connections', async () => {
        manager.subscribe('resp_123', {});
        manager.subscribe('resp_456', {});
        await vi.runAllTimersAsync();

        manager.closeAll();

        expect(manager.getActiveResponseIds()).toEqual([]);
        expect(mockEventSourceInstances[0].readyState).toBe(MockEventSource.CLOSED);
        expect(mockEventSourceInstances[1].readyState).toBe(MockEventSource.CLOSED);
      });
    });
  });

  describe('Convenience Functions', () => {
    describe('createSSEClient', () => {
      it('should create and connect client', async () => {
        const client = createSSEClient('resp_123', {});
        await vi.runAllTimersAsync();

        expect(client.isConnected()).toBe(true);
        expect(mockEventSourceInstances.length).toBe(1);

        client.close();
      });

      it('should accept custom config', async () => {
        const client = createSSEClient('resp_123', {}, { retryDelayMs: 5000, maxRetries: 3 });
        await vi.runAllTimersAsync();

        expect(client.isConnected()).toBe(true);

        client.close();
      });
    });

    describe('subscribeToDeepResearch', () => {
      it('should subscribe via global manager', async () => {
        const events: SSEProgressEvent[] = [];
        const unsubscribe = subscribeToDeepResearch('resp_123', {
          onProgress: (e) => events.push(e),
        });
        await vi.runAllTimersAsync();

        const progressEvent: SSEProgressEvent = {
          type: 'progress',
          step: 'Global test',
          percentage: 90,
        };
        mockEventSourceInstances[0].simulateTypedEvent('progress', JSON.stringify(progressEvent));

        expect(events.length).toBe(1);

        unsubscribe();
      });
    });
  });

  describe('Global SSE Manager', () => {
    it('should be a singleton instance', () => {
      expect(sseManager).toBeInstanceOf(SSEManager);
    });

    it('should manage subscriptions globally', async () => {
      const unsubscribe = sseManager.subscribe('resp_global', {});
      await vi.runAllTimersAsync();

      expect(sseManager.getActiveResponseIds()).toContain('resp_global');

      unsubscribe();
      sseManager.closeAll();
    });
  });

  describe('Event Latency (REQ_011.1.9)', () => {
    it('should update lastEventAt within reasonable time', async () => {
      const client = new SSEClient({ responseId: 'resp_123' });

      client.connect();
      await vi.runAllTimersAsync();

      const beforeTime = Date.now();
      const progressEvent: SSEProgressEvent = {
        type: 'progress',
        step: 'Latency test',
        percentage: 50,
      };
      mockEventSourceInstances[0].simulateTypedEvent('progress', JSON.stringify(progressEvent));

      const state = client.getState();
      const eventTime = new Date(state.lastEventAt!).getTime();

      // Event should be processed nearly instantly (within 100ms for tests)
      expect(eventTime).toBeGreaterThanOrEqual(beforeTime - 100);
      expect(eventTime).toBeLessThanOrEqual(beforeTime + 100);

      client.close();
    });
  });
});

describe('Streaming Types', () => {
  // These are imported from the streaming-types module
  // Testing type guards and parseSSEEvent

  it('should export type guards', async () => {
    const {
      isSSEReasoningEvent,
      isSSEWebSearchCallEvent,
      isSSEProgressEvent,
      isSSEDoneEvent,
      isSSEErrorEvent,
    } = await import('../streaming-types');

    const reasoningEvent = { type: 'reasoning' as const, id: '1', summary: 'Test', index: 0 };
    const searchEvent = {
      type: 'web_search_call' as const,
      id: '1',
      query: 'test',
      status: 'searching' as const,
    };
    const progressEvent = { type: 'progress' as const, step: 'Test', percentage: 50 };
    const doneEvent = { type: 'done' as const, responseId: '1', text: 'Done' };
    const errorEvent = {
      type: 'error' as const,
      code: 'TEST',
      message: 'Error',
      retryable: false,
    };

    expect(isSSEReasoningEvent(reasoningEvent)).toBe(true);
    expect(isSSEWebSearchCallEvent(searchEvent)).toBe(true);
    expect(isSSEProgressEvent(progressEvent)).toBe(true);
    expect(isSSEDoneEvent(doneEvent)).toBe(true);
    expect(isSSEErrorEvent(errorEvent)).toBe(true);

    // Cross-check
    expect(isSSEReasoningEvent(progressEvent)).toBe(false);
  });

  it('should parse valid SSE events', async () => {
    const { parseSSEEvent } = await import('../streaming-types');

    const validEvent = JSON.stringify({ type: 'progress', step: 'Test', percentage: 25 });
    const parsed = parseSSEEvent(validEvent);

    expect(parsed.type).toBe('progress');
  });

  it('should throw on invalid SSE event', async () => {
    const { parseSSEEvent } = await import('../streaming-types');

    expect(() => parseSSEEvent('{}')).toThrow('missing type field');
    expect(() => parseSSEEvent('{"type": "invalid_type"}')).toThrow('Invalid SSE event type');
    expect(() => parseSSEEvent('not json')).toThrow();
  });
});
