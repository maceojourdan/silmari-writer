/**
 * writingFlow - Module state management for the writing flow step navigation.
 *
 * Resource: ui-v3n6 (module)
 * Path: 331-return-to-recall-from-review
 *
 * Manages the state transitions for writing flow:
 * - Tracks active step (RECALL or REVIEW)
 * - Handles navigation intent from child components
 * - Guards against invalid state transitions
 */

import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type WritingFlowStep = 'RECALL' | 'REVIEW';

export interface NavigationIntent {
  targetStep: WritingFlowStep;
}

export interface WritingFlowState {
  activeStep: WritingFlowStep;
}

// ---------------------------------------------------------------------------
// State Validation
// ---------------------------------------------------------------------------

const VALID_STEPS = new Set<string>(['RECALL', 'REVIEW']);

export function isValidFlowState(state: unknown): state is WritingFlowState {
  if (!state || typeof state !== 'object') return false;
  const s = state as Record<string, unknown>;
  return typeof s.activeStep === 'string' && VALID_STEPS.has(s.activeStep);
}

// ---------------------------------------------------------------------------
// Navigation Handler
// ---------------------------------------------------------------------------

/**
 * Processes a navigation intent and returns the new state.
 * Returns null if the current state is invalid (error case).
 */
export function handleNavigation(
  currentState: WritingFlowState | undefined | null,
  intent: NavigationIntent,
): WritingFlowState | null {
  if (!isValidFlowState(currentState)) {
    frontendLogger.error(
      'Invalid flow state',
      new Error(`Cannot navigate: current state is invalid`),
      { module: 'WritingFlowModule', action: 'handleNavigation' },
    );
    return null;
  }

  return { activeStep: intent.targetStep };
}

// ---------------------------------------------------------------------------
// Initial State Factory
// ---------------------------------------------------------------------------

export function createInitialFlowState(
  initialStep: WritingFlowStep = 'REVIEW',
): WritingFlowState {
  return { activeStep: initialStep };
}
