/**
 * WorkflowErrors - Backend error definitions for workflow persistence
 * and transition failures.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 318-complete-voice-answer-advances-workflow
 */

export type WorkflowErrorCode =
  | 'PERSISTENCE_FAILED'
  | 'TRANSITION_FAILED';

export class WorkflowError extends Error {
  code: WorkflowErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: WorkflowErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'WorkflowError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 4: Persist completed slot set — persistence failure
// ---------------------------------------------------------------------------

export const WorkflowPersistenceError = {
  PERSISTENCE_FAILED: (message = 'Failed to persist completed slots') =>
    new WorkflowError(message, 'PERSISTENCE_FAILED', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Step 5: Advance workflow — transition failure
// ---------------------------------------------------------------------------

export const WorkflowTransitionError = {
  TRANSITION_FAILED: (message = 'Failed to transition to next workflow step') =>
    new WorkflowError(message, 'TRANSITION_FAILED', 500, false),
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate — all error factories
// ---------------------------------------------------------------------------

export const WorkflowErrors = {
  ...WorkflowPersistenceError,
  ...WorkflowTransitionError,
} as const;
