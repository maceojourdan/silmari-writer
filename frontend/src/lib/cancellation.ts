/**
 * Operation Cancellation Module (REQ_011.5)
 *
 * Handles cancellation of long-running operations with proper cleanup.
 */

// =============================================================================
// Constants
// =============================================================================

/** Maximum time to wait for cancellation to complete (ms) */
export const CANCELLATION_TIMEOUT_MS = 2000;

/** Debounce time to prevent double-click (ms) */
export const CANCELLATION_DEBOUNCE_MS = 500;

// =============================================================================
// Types
// =============================================================================

/**
 * Cancellation reason types
 * REQ_011.5.11: Track reason for analytics
 */
export type CancellationReason = 'user_initiated' | 'timeout' | 'error' | 'system';

/**
 * Cancellation status
 */
export type CancellationStatus = 'idle' | 'cancelling' | 'cancelled' | 'failed';

/**
 * Operation types that can be cancelled
 */
export type CancellableOperationType = 'deep_research' | 'image_generation' | 'document_generation';

/**
 * Intermediate result that can be preserved
 * REQ_011.5.5: Preserve partial results before cancellation
 */
export interface IntermediateResult {
  /** Type of intermediate result */
  type: 'text' | 'reasoning' | 'search_result' | 'partial_image' | 'partial_document';
  /** Content of the result */
  content: string;
  /** Timestamp when result was captured */
  capturedAt: string;
  /** Progress percentage at time of capture */
  progress?: number;
}

/**
 * Cancellation state for tracking active cancellations
 * REQ_011.5.3: Track 'Cancelling...' state
 */
export interface CancellationState {
  /** Operation ID being cancelled */
  operationId: string;
  /** Current cancellation status */
  status: CancellationStatus;
  /** Reason for cancellation */
  reason: CancellationReason;
  /** When cancellation was initiated */
  initiatedAt: string;
  /** When cancellation completed */
  completedAt?: string;
  /** Preserved intermediate results */
  preservedResults?: IntermediateResult[];
  /** Cost incurred before cancellation */
  incurredCost?: number;
}

/**
 * Cancellation request
 */
export interface CancellationRequest {
  /** Operation ID to cancel */
  operationId: string;
  /** Type of operation */
  operationType: CancellableOperationType;
  /** Reason for cancellation */
  reason?: CancellationReason;
}

/**
 * Cancellation response
 * REQ_011.5.9: Confirm when cancellation completes
 */
export interface CancellationResponse {
  /** Whether cancellation was successful */
  success: boolean;
  /** Operation ID that was cancelled */
  operationId: string;
  /** Preserved partial results */
  preservedResults?: IntermediateResult[];
  /** Cost incurred before cancellation */
  incurredCost?: number;
  /** Human-readable message */
  message: string;
}

/**
 * Cancellation handler options
 */
export interface CancellationHandlerOptions {
  /** Operation ID to cancel */
  operationId: string;
  /** Type of operation */
  operationType: CancellableOperationType;
  /** AbortController for the operation */
  abortController: AbortController;
  /** SSE client to close (if applicable) */
  sseClient?: { close: () => void };
  /** Callback to get current intermediate results */
  getIntermediateResults?: () => IntermediateResult[];
  /** Callback to get current cost */
  getCurrentCost?: () => number;
  /** Cleanup functions for resources */
  cleanupFunctions?: Array<() => Promise<void> | void>;
  /** Callback when cancellation starts */
  onCancelling?: () => void;
  /** Callback when cancellation completes */
  onCancelled?: (response: CancellationResponse) => void;
  /** Callback on cancellation error */
  onError?: (error: Error) => void;
}

/**
 * Active cancellation tracker
 */
interface ActiveCancellation {
  operationId: string;
  startedAt: number;
  state: CancellationState;
}

// =============================================================================
// Cancellation Manager
// =============================================================================

/**
 * Manages cancellation of long-running operations
 * REQ_011.5: Proper cleanup of resources
 */
export class CancellationManager {
  private activeCancellations: Map<string, ActiveCancellation> = new Map();
  private lastCancellationAttempt: Map<string, number> = new Map();

  /**
   * Check if operation can be cancelled (not already cancelling)
   * REQ_011.5.13: Prevent double-click
   */
  canCancel(operationId: string): boolean {
    const active = this.activeCancellations.get(operationId);
    if (active && active.state.status === 'cancelling') {
      return false;
    }

    // Debounce check
    const lastAttempt = this.lastCancellationAttempt.get(operationId);
    if (lastAttempt && Date.now() - lastAttempt < CANCELLATION_DEBOUNCE_MS) {
      return false;
    }

    return true;
  }

  /**
   * Cancel an operation
   * REQ_011.5: Main cancellation entry point
   */
  async cancel(options: CancellationHandlerOptions): Promise<CancellationResponse> {
    const {
      operationId,
      operationType,
      abortController,
      sseClient,
      getIntermediateResults,
      getCurrentCost,
      cleanupFunctions,
      onCancelling,
      onCancelled,
      onError,
    } = options;

    // REQ_011.5.13: Prevent double-click
    if (!this.canCancel(operationId)) {
      return {
        success: false,
        operationId,
        message: 'Cancellation already in progress',
      };
    }

    this.lastCancellationAttempt.set(operationId, Date.now());

    // Initialize cancellation state
    const state: CancellationState = {
      operationId,
      status: 'cancelling',
      reason: 'user_initiated',
      initiatedAt: new Date().toISOString(),
    };

    this.activeCancellations.set(operationId, {
      operationId,
      startedAt: Date.now(),
      state,
    });

    // REQ_011.5.3: Show 'Cancelling...' state
    onCancelling?.();

    try {
      // REQ_011.5.5: Preserve partial results
      const preservedResults = getIntermediateResults?.() || [];

      // REQ_011.5.10: Track cost
      const incurredCost = getCurrentCost?.() || 0;

      // REQ_011.5.4: Stop API streaming/polling within 2 seconds
      const cancellationPromise = this.performCancellation(
        operationId,
        operationType,
        abortController,
        sseClient,
        cleanupFunctions
      );

      // Timeout for cancellation
      const timeoutPromise = new Promise<void>((_, reject) => {
        setTimeout(() => reject(new Error('Cancellation timeout')), CANCELLATION_TIMEOUT_MS);
      });

      await Promise.race([cancellationPromise, timeoutPromise]).catch((error) => {
        console.warn(`[CancellationManager] Cancellation warning: ${error.message}`);
        // Force abort even on timeout
        abortController.abort();
        sseClient?.close();
      });

      // REQ_011.5.11: Log cancellation
      this.logCancellation(operationId, operationType, 'user_initiated', incurredCost);

      // Update state
      state.status = 'cancelled';
      state.completedAt = new Date().toISOString();
      state.preservedResults = preservedResults;
      state.incurredCost = incurredCost;

      const response: CancellationResponse = {
        success: true,
        operationId,
        preservedResults,
        incurredCost,
        message: 'Operation cancelled successfully',
      };

      // REQ_011.5.9: Confirm cancellation
      onCancelled?.(response);

      // REQ_011.5.12: Clean up state for new operations
      this.activeCancellations.delete(operationId);

      return response;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';

      state.status = 'failed';
      this.activeCancellations.delete(operationId);

      onError?.(error instanceof Error ? error : new Error(errorMessage));

      return {
        success: false,
        operationId,
        message: `Cancellation failed: ${errorMessage}`,
      };
    }
  }

  /**
   * Perform the actual cancellation
   * REQ_011.5.4-8: Cleanup resources
   */
  private async performCancellation(
    operationId: string,
    operationType: CancellableOperationType,
    abortController: AbortController,
    sseClient?: { close: () => void },
    cleanupFunctions?: Array<() => Promise<void> | void>
  ): Promise<void> {
    // REQ_011.5.15: Propagate abort signal
    abortController.abort();

    // REQ_011.5.14: Close SSE connection
    sseClient?.close();

    // Run cleanup functions in parallel
    const cleanupPromises: Promise<void>[] = [];

    // REQ_011.5.6: Cleanup OpenAI background job (if applicable)
    if (operationType === 'deep_research') {
      cleanupPromises.push(this.cleanupOpenAIJob(operationId));
    }

    // REQ_011.5.7: Cleanup Vercel blobs (if applicable)
    if (operationType === 'image_generation') {
      cleanupPromises.push(this.cleanupVercelBlobs(operationId));
    }

    // REQ_011.5.8: Cleanup temp files (if applicable)
    if (operationType === 'document_generation') {
      cleanupPromises.push(this.cleanupTempFiles(operationId));
    }

    // Run custom cleanup functions
    if (cleanupFunctions) {
      for (const cleanup of cleanupFunctions) {
        cleanupPromises.push(Promise.resolve(cleanup()));
      }
    }

    // Wait for all cleanup to complete (with individual error handling)
    await Promise.allSettled(cleanupPromises);
  }

  /**
   * Clean up OpenAI background job
   * REQ_011.5.6: Cancel Deep Research job
   */
  private async cleanupOpenAIJob(operationId: string): Promise<void> {
    try {
      // Note: OpenAI doesn't currently support cancelling background jobs
      // This is a placeholder for when that feature becomes available
      // For now, we just stop polling on our end
      console.log(`[CancellationManager] Stopped polling for job: ${operationId}`);
    } catch (error) {
      console.warn(`[CancellationManager] Failed to cleanup OpenAI job: ${operationId}`, error);
    }
  }

  /**
   * Clean up partial Vercel blobs
   * REQ_011.5.7: Remove partial image uploads
   */
  private async cleanupVercelBlobs(operationId: string): Promise<void> {
    try {
      // Call cleanup endpoint
      await fetch('/api/cleanup/blobs', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ operationId }),
      }).catch(() => {
        // Ignore cleanup failures - they'll be cleaned up by TTL
      });
    } catch (error) {
      console.warn(`[CancellationManager] Failed to cleanup blobs: ${operationId}`, error);
    }
  }

  /**
   * Clean up temporary files
   * REQ_011.5.8: Remove temp document files
   */
  private async cleanupTempFiles(operationId: string): Promise<void> {
    try {
      // Call cleanup endpoint
      await fetch('/api/cleanup/temp', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ operationId }),
      }).catch(() => {
        // Ignore cleanup failures
      });
    } catch (error) {
      console.warn(`[CancellationManager] Failed to cleanup temp files: ${operationId}`, error);
    }
  }

  /**
   * Log cancellation for analytics
   * REQ_011.5.11: Track reason
   */
  private logCancellation(
    operationId: string,
    operationType: string,
    reason: CancellationReason,
    incurredCost: number
  ): void {
    const logEntry = {
      timestamp: new Date().toISOString(),
      operationId,
      operationType,
      reason,
      incurredCost,
      event: 'operation_cancelled',
    };

    console.log('[CancellationAnalytics]', JSON.stringify(logEntry));
  }

  /**
   * Get cancellation state for an operation
   */
  getCancellationState(operationId: string): CancellationState | null {
    const active = this.activeCancellations.get(operationId);
    return active?.state || null;
  }

  /**
   * Check if an operation is being cancelled
   */
  isCancelling(operationId: string): boolean {
    const active = this.activeCancellations.get(operationId);
    return active?.state.status === 'cancelling';
  }

  /**
   * Cancel due to timeout
   * REQ_011.5.11: Timeout reason
   */
  async cancelDueToTimeout(options: Omit<CancellationHandlerOptions, 'onCancelling'>): Promise<CancellationResponse> {
    const state = this.activeCancellations.get(options.operationId);
    if (state) {
      state.state.reason = 'timeout';
    }

    return this.cancel({
      ...options,
      onCancelling: () => {
        // Don't show cancelling state for timeout
      },
    });
  }

  /**
   * Cancel due to error
   * REQ_011.5.11: Error reason
   */
  async cancelDueToError(
    options: Omit<CancellationHandlerOptions, 'onCancelling'>,
    error: Error
  ): Promise<CancellationResponse> {
    const state = this.activeCancellations.get(options.operationId);
    if (state) {
      state.state.reason = 'error';
    }

    console.error(`[CancellationManager] Cancelling due to error: ${error.message}`);

    return this.cancel({
      ...options,
      onCancelling: () => {
        // Don't show cancelling state for errors
      },
    });
  }

  /**
   * Clear all active cancellations (for testing)
   */
  clearAll(): void {
    this.activeCancellations.clear();
    this.lastCancellationAttempt.clear();
  }
}

/**
 * Global cancellation manager instance
 */
export const cancellationManager = new CancellationManager();

// =============================================================================
// React Hook Support
// =============================================================================

/**
 * Cancellation hook state
 */
export interface UseCancellationState {
  isCancelling: boolean;
  canCancel: boolean;
  error: string | null;
}

/**
 * Create initial cancellation state
 */
export function createCancellationState(): UseCancellationState {
  return {
    isCancelling: false,
    canCancel: true,
    error: null,
  };
}

// =============================================================================
// Convenience Functions
// =============================================================================

/**
 * Create an AbortController for an operation
 * REQ_011.5.15: AbortController signal propagation
 */
export function createOperationAbortController(): {
  controller: AbortController;
  signal: AbortSignal;
  abort: () => void;
  isAborted: () => boolean;
} {
  const controller = new AbortController();
  return {
    controller,
    signal: controller.signal,
    abort: () => controller.abort(),
    isAborted: () => controller.signal.aborted,
  };
}

/**
 * Wrap a fetch call with abort signal
 */
export function fetchWithAbort(
  url: string,
  init: RequestInit,
  signal: AbortSignal
): Promise<Response> {
  return fetch(url, { ...init, signal });
}

/**
 * Check if an error is an abort error
 */
export function isAbortError(error: unknown): boolean {
  if (error instanceof DOMException && error.name === 'AbortError') {
    return true;
  }
  if (error instanceof Error && error.name === 'AbortError') {
    return true;
  }
  return false;
}

/**
 * Create an intermediate result for preservation
 * REQ_011.5.5: Helper for creating intermediate results
 */
export function createIntermediateResult(
  type: IntermediateResult['type'],
  content: string,
  progress?: number
): IntermediateResult {
  return {
    type,
    content,
    capturedAt: new Date().toISOString(),
    progress,
  };
}

/**
 * Merge multiple intermediate results
 * REQ_011.5.5: Combine partial results
 */
export function mergeIntermediateResults(results: IntermediateResult[]): string {
  return results
    .sort((a, b) => a.capturedAt.localeCompare(b.capturedAt))
    .map(r => r.content)
    .join('\n\n');
}
