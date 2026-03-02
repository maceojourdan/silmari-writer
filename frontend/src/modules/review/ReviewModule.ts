/**
 * ReviewModule - State management for the review screen with voice edit support.
 *
 * Manages:
 *   - Content preservation during voice edit flows
 *   - Voice session state (capturing, idle, error) with attempt tracking
 *   - Snapshot/restore mechanism to guard against unintended mutations
 *
 * Resource: ui-v3n6 (module)
 * Path: 332-voice-edit-no-input-error-on-review-screen
 */

import type { VoiceErrorDef } from '@/server/error_definitions/VoiceErrors';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type VoiceSession = {
  status: 'capturing' | 'idle' | 'error';
  attempts: number;
};

export interface ReviewState {
  content: string;
  voiceSession: VoiceSession | null;
  error: VoiceErrorDef | null;
}

// ---------------------------------------------------------------------------
// Module
// ---------------------------------------------------------------------------

export class ReviewModule {
  private state: ReviewState;
  private lastStableState: ReviewState;

  constructor(content: string) {
    this.state = {
      content,
      voiceSession: null,
      error: null,
    };
    this.lastStableState = structuredClone(this.state);
  }

  // -------------------------------------------------------------------------
  // Getters
  // -------------------------------------------------------------------------

  getState(): ReviewState {
    return this.state;
  }

  // -------------------------------------------------------------------------
  // Snapshot / Restore
  // -------------------------------------------------------------------------

  /**
   * Takes a snapshot of the current stable state.
   * Called automatically when entering voice mode.
   */
  snapshot(): void {
    this.lastStableState = structuredClone(this.state);
  }

  /**
   * Restores the last known stable state.
   * Used on unintended mutation detection or explicit recovery.
   */
  restore(): void {
    this.state = structuredClone(this.lastStableState);
  }

  /**
   * Guards against unintended content mutation by comparing current
   * content to the snapshot and restoring if different.
   */
  guardState(): void {
    if (this.state.content !== this.lastStableState.content) {
      this.restore();
    }
  }

  // -------------------------------------------------------------------------
  // Voice Session Management
  // -------------------------------------------------------------------------

  /**
   * Initializes a voice capture session.
   * Takes a snapshot of current state before entering voice mode.
   * Preserves attempt count across sessions.
   */
  startVoiceSession(): void {
    // Snapshot current stable state before voice mode
    this.snapshot();

    const currentAttempts = this.state.voiceSession?.attempts ?? 0;

    this.state = {
      ...this.state,
      voiceSession: {
        status: 'capturing',
        attempts: currentAttempts,
      },
      error: null,
    };
  }

  /**
   * Handles a voice validation error.
   * Increments attempt count, resets voice mode to idle, sets error.
   * Content is preserved from the snapshot.
   */
  handleVoiceError(error: VoiceErrorDef): void {
    const currentAttempts = this.state.voiceSession?.attempts ?? 0;

    this.state = {
      ...this.state,
      content: this.lastStableState.content, // Ensure content preserved
      voiceSession: {
        status: 'idle',
        attempts: currentAttempts + 1,
      },
      error,
    };
  }

  // -------------------------------------------------------------------------
  // Test Helpers
  // -------------------------------------------------------------------------

  /**
   * Simulates an unintended mutation for testing purposes.
   * In production, this would be an unexpected state change from a bug.
   */
  simulateMutation(newContent: string): void {
    this.state = {
      ...this.state,
      content: newContent,
    };
  }
}
