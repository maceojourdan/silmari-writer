/**
 * confirmStorySelectionLoader - Manages the story confirmation API call
 * with cancellation support for race condition handling.
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * Provides confirm() to send the confirmation request and cancel()
 * to abort any in-flight request when validation fails after initiation.
 */

import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface ConfirmStorySelectionResult {
  confirmedStoryId: string;
  status: string;
}

// ---------------------------------------------------------------------------
// Loader
// ---------------------------------------------------------------------------

let abortController: AbortController | null = null;

export const confirmStorySelectionLoader = {
  /**
   * Send a story confirmation request to the backend.
   *
   * @param storyId - The ID of the story to confirm
   * @returns The confirmation result
   * @throws Error on network failure or server error
   */
  async confirm(storyId: string): Promise<ConfirmStorySelectionResult> {
    // Cancel any existing in-flight request
    if (abortController) {
      abortController.abort();
    }

    abortController = new AbortController();

    try {
      const response = await fetch('/api/story/confirm', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ storyId }),
        signal: abortController.signal,
      });

      if (!response.ok) {
        const errorBody = await response.json().catch(() => ({}));
        throw new Error(
          errorBody.message || `Story confirmation failed with status ${response.status}`,
        );
      }

      const data = await response.json();
      return data as ConfirmStorySelectionResult;
    } catch (err) {
      if (err instanceof DOMException && err.name === 'AbortError') {
        frontendLogger.info('Confirmation request cancelled', {
          module: 'confirmStorySelectionLoader',
          action: 'cancel',
        });
        throw err;
      }
      throw err;
    } finally {
      abortController = null;
    }
  },

  /**
   * Cancel any in-flight confirmation request.
   * Used when validation fails after a request was already initiated (race condition).
   */
  cancel(): void {
    if (abortController) {
      abortController.abort();
      abortController = null;
      frontendLogger.info('In-flight confirmation request cancelled', {
        module: 'confirmStorySelectionLoader',
        action: 'cancel',
      });
    }
  },
} as const;
