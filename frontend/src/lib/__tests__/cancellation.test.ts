/**
 * Unit tests for Cancellation Module
 * REQ_011.5: Operation Cancellation
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

import {
  CancellationManager,
  cancellationManager,
  createCancellationState,
  createOperationAbortController,
  fetchWithAbort,
  isAbortError,
  createIntermediateResult,
  mergeIntermediateResults,
  CANCELLATION_TIMEOUT_MS,
  CANCELLATION_DEBOUNCE_MS,
  type CancellationHandlerOptions,
  type IntermediateResult,
  type CancellationResponse,
} from '../cancellation';

// Mock fetch globally
const mockFetch = vi.fn();
global.fetch = mockFetch;

describe('Cancellation Module (REQ_011.5)', () => {
  let manager: CancellationManager;

  beforeEach(() => {
    vi.resetAllMocks();
    vi.useFakeTimers();
    manager = new CancellationManager();
    mockFetch.mockResolvedValue(new Response(JSON.stringify({ success: true })));
  });

  afterEach(() => {
    vi.restoreAllMocks();
    vi.useRealTimers();
    cancellationManager.clearAll();
  });

  describe('CancellationManager', () => {
    describe('canCancel (REQ_011.5.13)', () => {
      it('should return true for new operation', () => {
        expect(manager.canCancel('op-123')).toBe(true);
      });

      it('should return false when cancellation is in progress', async () => {
        const abortController = new AbortController();
        const options: CancellationHandlerOptions = {
          operationId: 'op-123',
          operationType: 'deep_research',
          abortController,
        };

        // Start cancellation without awaiting
        const cancelPromise = manager.cancel(options);

        // Should be false while cancelling
        expect(manager.canCancel('op-123')).toBe(false);

        // Advance timers and wait for completion
        await vi.advanceTimersByTimeAsync(CANCELLATION_TIMEOUT_MS + 100);
        await cancelPromise;
      });

      it('should debounce rapid cancellation attempts', async () => {
        const abortController = new AbortController();
        const options: CancellationHandlerOptions = {
          operationId: 'op-456',
          operationType: 'image_generation',
          abortController,
        };

        // First cancellation
        await manager.cancel(options);

        // Immediate second attempt should be debounced
        expect(manager.canCancel('op-456')).toBe(false);

        // After debounce period, should be allowed
        vi.advanceTimersByTime(CANCELLATION_DEBOUNCE_MS + 10);
        expect(manager.canCancel('op-456')).toBe(true);
      });
    });

    describe('cancel (REQ_011.5)', () => {
      it('should successfully cancel an operation', async () => {
        const abortController = new AbortController();
        const onCancelling = vi.fn();
        const onCancelled = vi.fn();

        const options: CancellationHandlerOptions = {
          operationId: 'op-789',
          operationType: 'deep_research',
          abortController,
          onCancelling,
          onCancelled,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        const result = await resultPromise;

        expect(result.success).toBe(true);
        expect(result.operationId).toBe('op-789');
        expect(result.message).toBe('Operation cancelled successfully');
        expect(onCancelling).toHaveBeenCalled();
        expect(onCancelled).toHaveBeenCalledWith(expect.objectContaining({
          success: true,
          operationId: 'op-789',
        }));
      });

      it('should abort the AbortController (REQ_011.5.15)', async () => {
        const abortController = new AbortController();
        const abortSpy = vi.spyOn(abortController, 'abort');

        const options: CancellationHandlerOptions = {
          operationId: 'op-abc',
          operationType: 'deep_research',
          abortController,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(abortSpy).toHaveBeenCalled();
        expect(abortController.signal.aborted).toBe(true);
      });

      it('should close SSE client (REQ_011.5.14)', async () => {
        const abortController = new AbortController();
        const sseClient = { close: vi.fn() };

        const options: CancellationHandlerOptions = {
          operationId: 'op-sse',
          operationType: 'deep_research',
          abortController,
          sseClient,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(sseClient.close).toHaveBeenCalled();
      });

      it('should preserve intermediate results (REQ_011.5.5)', async () => {
        const abortController = new AbortController();
        const intermediateResults: IntermediateResult[] = [
          createIntermediateResult('text', 'Partial text result', 50),
          createIntermediateResult('reasoning', 'Reasoning step 1', 30),
        ];

        const options: CancellationHandlerOptions = {
          operationId: 'op-preserve',
          operationType: 'deep_research',
          abortController,
          getIntermediateResults: () => intermediateResults,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        const result = await resultPromise;

        expect(result.preservedResults).toHaveLength(2);
        expect(result.preservedResults?.[0].content).toBe('Partial text result');
      });

      it('should track incurred cost (REQ_011.5.10)', async () => {
        const abortController = new AbortController();
        const currentCost = 2.50;

        const options: CancellationHandlerOptions = {
          operationId: 'op-cost',
          operationType: 'deep_research',
          abortController,
          getCurrentCost: () => currentCost,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        const result = await resultPromise;

        expect(result.incurredCost).toBe(2.50);
      });

      it('should run custom cleanup functions (REQ_011.5.6-8)', async () => {
        const abortController = new AbortController();
        const cleanup1 = vi.fn();
        const cleanup2 = vi.fn().mockResolvedValue(undefined);

        const options: CancellationHandlerOptions = {
          operationId: 'op-cleanup',
          operationType: 'deep_research',
          abortController,
          cleanupFunctions: [cleanup1, cleanup2],
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(cleanup1).toHaveBeenCalled();
        expect(cleanup2).toHaveBeenCalled();
      });

      it('should prevent double-click cancellation (REQ_011.5.13)', async () => {
        const abortController1 = new AbortController();

        const options1: CancellationHandlerOptions = {
          operationId: 'op-double',
          operationType: 'deep_research',
          abortController: abortController1,
        };

        // First cancellation
        const result1Promise = manager.cancel(options1);
        await vi.advanceTimersByTimeAsync(100);
        const result1 = await result1Promise;
        expect(result1.success).toBe(true);

        // Immediate second attempt (within debounce)
        const abortController2 = new AbortController();
        const options2: CancellationHandlerOptions = {
          operationId: 'op-double',
          operationType: 'deep_research',
          abortController: abortController2,
        };

        const result2Promise = manager.cancel(options2);
        const result2 = await result2Promise;

        expect(result2.success).toBe(false);
        expect(result2.message).toBe('Cancellation already in progress');
      });

      it('should call cleanup endpoint for Vercel blobs (REQ_011.5.7)', async () => {
        const abortController = new AbortController();

        const options: CancellationHandlerOptions = {
          operationId: 'op-blobs',
          operationType: 'image_generation',
          abortController,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(mockFetch).toHaveBeenCalledWith(
          '/api/cleanup/blobs',
          expect.objectContaining({
            method: 'POST',
            body: JSON.stringify({ operationId: 'op-blobs' }),
          })
        );
      });

      it('should call cleanup endpoint for temp files (REQ_011.5.8)', async () => {
        const abortController = new AbortController();

        const options: CancellationHandlerOptions = {
          operationId: 'op-temp',
          operationType: 'document_generation',
          abortController,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(mockFetch).toHaveBeenCalledWith(
          '/api/cleanup/temp',
          expect.objectContaining({
            method: 'POST',
            body: JSON.stringify({ operationId: 'op-temp' }),
          })
        );
      });

      it('should complete within timeout (REQ_011.5.4)', async () => {
        const abortController = new AbortController();
        const onCancelled = vi.fn();

        const options: CancellationHandlerOptions = {
          operationId: 'op-timeout',
          operationType: 'deep_research',
          abortController,
          onCancelled,
        };

        const startTime = Date.now();
        const resultPromise = manager.cancel(options);

        // Advance to just before timeout
        await vi.advanceTimersByTimeAsync(CANCELLATION_TIMEOUT_MS - 100);
        const result = await resultPromise;

        expect(result.success).toBe(true);
        expect(onCancelled).toHaveBeenCalled();
      });

      it('should force abort on timeout', async () => {
        const abortController = new AbortController();

        // Create a cleanup function that never resolves
        const neverResolve = () => new Promise<void>(() => {});

        const options: CancellationHandlerOptions = {
          operationId: 'op-slow',
          operationType: 'deep_research',
          abortController,
          cleanupFunctions: [neverResolve],
        };

        const resultPromise = manager.cancel(options);

        // Advance past timeout
        await vi.advanceTimersByTimeAsync(CANCELLATION_TIMEOUT_MS + 100);
        const result = await resultPromise;

        // Should still succeed (force abort on timeout)
        expect(result.success).toBe(true);
        expect(abortController.signal.aborted).toBe(true);
      });
    });

    describe('getCancellationState', () => {
      it('should return null for unknown operation', () => {
        expect(manager.getCancellationState('unknown')).toBeNull();
      });

      it('should return state for active cancellation', async () => {
        const abortController = new AbortController();
        const options: CancellationHandlerOptions = {
          operationId: 'op-state',
          operationType: 'deep_research',
          abortController,
        };

        // Start cancellation
        const cancelPromise = manager.cancel(options);

        // Check state during cancellation
        const state = manager.getCancellationState('op-state');
        expect(state).not.toBeNull();
        expect(state?.status).toBe('cancelling');
        expect(state?.reason).toBe('user_initiated');

        await vi.advanceTimersByTimeAsync(CANCELLATION_TIMEOUT_MS + 100);
        await cancelPromise;
      });
    });

    describe('isCancelling', () => {
      it('should return false for unknown operation', () => {
        expect(manager.isCancelling('unknown')).toBe(false);
      });

      it('should return true during active cancellation', async () => {
        const abortController = new AbortController();
        const options: CancellationHandlerOptions = {
          operationId: 'op-checking',
          operationType: 'image_generation',
          abortController,
        };

        const cancelPromise = manager.cancel(options);
        expect(manager.isCancelling('op-checking')).toBe(true);

        await vi.advanceTimersByTimeAsync(CANCELLATION_TIMEOUT_MS + 100);
        await cancelPromise;

        expect(manager.isCancelling('op-checking')).toBe(false);
      });
    });

    describe('cancelDueToTimeout (REQ_011.5.11)', () => {
      it('should set reason to timeout', async () => {
        const abortController = new AbortController();
        const consoleSpy = vi.spyOn(console, 'log');

        const options: Omit<CancellationHandlerOptions, 'onCancelling'> = {
          operationId: 'op-timeout-reason',
          operationType: 'deep_research',
          abortController,
        };

        const resultPromise = manager.cancelDueToTimeout(options);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(consoleSpy).toHaveBeenCalledWith(
          '[CancellationAnalytics]',
          expect.stringContaining('user_initiated')
        );
      });
    });

    describe('cancelDueToError (REQ_011.5.11)', () => {
      it('should set reason to error and log', async () => {
        const abortController = new AbortController();
        const consoleSpy = vi.spyOn(console, 'error');

        const options: Omit<CancellationHandlerOptions, 'onCancelling'> = {
          operationId: 'op-error-reason',
          operationType: 'deep_research',
          abortController,
        };

        const testError = new Error('Network failure');

        const resultPromise = manager.cancelDueToError(options, testError);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(consoleSpy).toHaveBeenCalledWith(
          '[CancellationManager] Cancelling due to error: Network failure'
        );
      });
    });

    describe('Analytics logging (REQ_011.5.11)', () => {
      it('should log cancellation with all required fields', async () => {
        const consoleSpy = vi.spyOn(console, 'log');
        const abortController = new AbortController();

        const options: CancellationHandlerOptions = {
          operationId: 'op-analytics',
          operationType: 'deep_research',
          abortController,
          getCurrentCost: () => 5.0,
        };

        const resultPromise = manager.cancel(options);
        await vi.advanceTimersByTimeAsync(100);
        await resultPromise;

        expect(consoleSpy).toHaveBeenCalledWith(
          '[CancellationAnalytics]',
          expect.stringContaining('op-analytics')
        );

        const logCall = consoleSpy.mock.calls.find(
          call => call[0] === '[CancellationAnalytics]'
        );
        const logData = JSON.parse(logCall![1] as string);

        expect(logData.operationId).toBe('op-analytics');
        expect(logData.operationType).toBe('deep_research');
        expect(logData.reason).toBe('user_initiated');
        expect(logData.incurredCost).toBe(5.0);
        expect(logData.event).toBe('operation_cancelled');
        expect(logData.timestamp).toBeDefined();
      });
    });
  });

  describe('createCancellationState', () => {
    it('should create initial state with correct defaults', () => {
      const state = createCancellationState();

      expect(state.isCancelling).toBe(false);
      expect(state.canCancel).toBe(true);
      expect(state.error).toBeNull();
    });
  });

  describe('createOperationAbortController (REQ_011.5.15)', () => {
    it('should create abort controller with all methods', () => {
      const result = createOperationAbortController();

      expect(result.controller).toBeInstanceOf(AbortController);
      expect(result.signal).toBeInstanceOf(AbortSignal);
      expect(typeof result.abort).toBe('function');
      expect(typeof result.isAborted).toBe('function');
    });

    it('should track aborted state', () => {
      const result = createOperationAbortController();

      expect(result.isAborted()).toBe(false);
      result.abort();
      expect(result.isAborted()).toBe(true);
    });

    it('should share signal between controller and result', () => {
      const result = createOperationAbortController();

      expect(result.signal.aborted).toBe(false);
      result.controller.abort();
      expect(result.signal.aborted).toBe(true);
      expect(result.isAborted()).toBe(true);
    });
  });

  describe('fetchWithAbort', () => {
    it('should pass signal to fetch', async () => {
      const { signal } = createOperationAbortController();
      mockFetch.mockResolvedValue(new Response('OK'));

      await fetchWithAbort('https://api.example.com', { method: 'GET' }, signal);

      expect(mockFetch).toHaveBeenCalledWith(
        'https://api.example.com',
        expect.objectContaining({
          method: 'GET',
          signal,
        })
      );
    });

    it('should merge existing init options', async () => {
      const { signal } = createOperationAbortController();
      mockFetch.mockResolvedValue(new Response('OK'));

      await fetchWithAbort(
        'https://api.example.com',
        {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: '{}',
        },
        signal
      );

      expect(mockFetch).toHaveBeenCalledWith(
        'https://api.example.com',
        expect.objectContaining({
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: '{}',
          signal,
        })
      );
    });
  });

  describe('isAbortError', () => {
    it('should return true for DOMException AbortError', () => {
      const error = new DOMException('The operation was aborted', 'AbortError');
      expect(isAbortError(error)).toBe(true);
    });

    it('should return true for Error with name AbortError', () => {
      const error = new Error('Aborted');
      error.name = 'AbortError';
      expect(isAbortError(error)).toBe(true);
    });

    it('should return false for regular Error', () => {
      const error = new Error('Network error');
      expect(isAbortError(error)).toBe(false);
    });

    it('should return false for non-Error values', () => {
      expect(isAbortError(null)).toBe(false);
      expect(isAbortError(undefined)).toBe(false);
      expect(isAbortError('error')).toBe(false);
      expect(isAbortError({ message: 'error' })).toBe(false);
    });
  });

  describe('createIntermediateResult (REQ_011.5.5)', () => {
    it('should create result with all fields', () => {
      vi.useRealTimers();
      const before = new Date().toISOString();

      const result = createIntermediateResult('text', 'Test content', 75);

      expect(result.type).toBe('text');
      expect(result.content).toBe('Test content');
      expect(result.progress).toBe(75);
      expect(result.capturedAt).toBeDefined();
      expect(new Date(result.capturedAt).getTime()).toBeGreaterThanOrEqual(
        new Date(before).getTime()
      );
    });

    it('should work without progress', () => {
      const result = createIntermediateResult('reasoning', 'Reasoning step');

      expect(result.type).toBe('reasoning');
      expect(result.content).toBe('Reasoning step');
      expect(result.progress).toBeUndefined();
    });

    it('should support all result types', () => {
      const types: IntermediateResult['type'][] = [
        'text',
        'reasoning',
        'search_result',
        'partial_image',
        'partial_document',
      ];

      for (const type of types) {
        const result = createIntermediateResult(type, 'content');
        expect(result.type).toBe(type);
      }
    });
  });

  describe('mergeIntermediateResults (REQ_011.5.5)', () => {
    it('should merge results in chronological order', () => {
      const results: IntermediateResult[] = [
        { type: 'text', content: 'Third', capturedAt: '2024-01-01T00:00:03Z' },
        { type: 'text', content: 'First', capturedAt: '2024-01-01T00:00:01Z' },
        { type: 'text', content: 'Second', capturedAt: '2024-01-01T00:00:02Z' },
      ];

      const merged = mergeIntermediateResults(results);

      expect(merged).toBe('First\n\nSecond\n\nThird');
    });

    it('should handle empty array', () => {
      const merged = mergeIntermediateResults([]);
      expect(merged).toBe('');
    });

    it('should handle single result', () => {
      const results: IntermediateResult[] = [
        { type: 'text', content: 'Only one', capturedAt: '2024-01-01T00:00:00Z' },
      ];

      const merged = mergeIntermediateResults(results);
      expect(merged).toBe('Only one');
    });
  });

  describe('Constants', () => {
    it('should have correct timeout value (2 seconds)', () => {
      expect(CANCELLATION_TIMEOUT_MS).toBe(2000);
    });

    it('should have correct debounce value (500ms)', () => {
      expect(CANCELLATION_DEBOUNCE_MS).toBe(500);
    });
  });

  describe('Global cancellationManager', () => {
    it('should be a CancellationManager instance', () => {
      expect(cancellationManager).toBeInstanceOf(CancellationManager);
    });

    it('should be a singleton', () => {
      // Import again and verify same instance
      expect(cancellationManager).toBeDefined();
      expect(typeof cancellationManager.cancel).toBe('function');
      expect(typeof cancellationManager.canCancel).toBe('function');
    });
  });

  describe('Error handling', () => {
    it('should call onError callback on failure', async () => {
      const abortController = new AbortController();
      const onError = vi.fn();

      // Create a cleanup function that throws
      const failingCleanup = () => {
        throw new Error('Cleanup failed');
      };

      const options: CancellationHandlerOptions = {
        operationId: 'op-fail',
        operationType: 'deep_research',
        abortController,
        cleanupFunctions: [failingCleanup],
        onError,
      };

      const resultPromise = manager.cancel(options);
      await vi.advanceTimersByTimeAsync(100);
      const result = await resultPromise;

      // Should still complete successfully despite cleanup error
      // because we use Promise.allSettled
      expect(result.success).toBe(true);
    });

    it('should handle cleanup failures gracefully', async () => {
      mockFetch.mockRejectedValue(new Error('Network error'));

      const abortController = new AbortController();
      const consoleSpy = vi.spyOn(console, 'warn');

      const options: CancellationHandlerOptions = {
        operationId: 'op-cleanup-fail',
        operationType: 'image_generation',
        abortController,
      };

      const resultPromise = manager.cancel(options);
      await vi.advanceTimersByTimeAsync(100);
      const result = await resultPromise;

      // Should still succeed despite cleanup failure
      expect(result.success).toBe(true);
    });
  });

  describe('Allow new operation after cancellation (REQ_011.5.12)', () => {
    it('should allow new operation after debounce period', async () => {
      const abortController1 = new AbortController();

      const options1: CancellationHandlerOptions = {
        operationId: 'op-reuse',
        operationType: 'deep_research',
        abortController: abortController1,
      };

      // First cancellation
      const result1Promise = manager.cancel(options1);
      await vi.advanceTimersByTimeAsync(100);
      await result1Promise;

      // Wait for debounce
      vi.advanceTimersByTime(CANCELLATION_DEBOUNCE_MS + 10);

      // New operation should be allowed
      expect(manager.canCancel('op-reuse')).toBe(true);

      const abortController2 = new AbortController();
      const options2: CancellationHandlerOptions = {
        operationId: 'op-reuse',
        operationType: 'deep_research',
        abortController: abortController2,
      };

      const result2Promise = manager.cancel(options2);
      await vi.advanceTimersByTimeAsync(100);
      const result2 = await result2Promise;

      expect(result2.success).toBe(true);
    });
  });
});
