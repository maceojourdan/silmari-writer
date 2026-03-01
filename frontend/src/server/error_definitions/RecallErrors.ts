/**
 * RecallErrors - Structured error definitions for the recall completion path.
 *
 * Provides typed error factories for parsing, validation, state-transition,
 * and incomplete-information failures during the recall slot completion flow.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 319-complete-required-slots-and-end-recall-loop
 */

// ---------------------------------------------------------------------------
// Error codes
// ---------------------------------------------------------------------------

export type RecallErrorCode =
  | 'INVALID_RECALL_STATE'
  | 'SLOT_PARSING_ERROR'
  | 'SLOT_VALIDATION_ERROR'
  | 'RECALL_STATE_TRANSITION_ERROR'
  | 'INCOMPLETE_INFORMATION_ERROR';

// ---------------------------------------------------------------------------
// Base RecallError class
// ---------------------------------------------------------------------------

export class RecallError extends Error {
  code: RecallErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: RecallErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'RecallError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 1: No active recall session
// ---------------------------------------------------------------------------

export const InvalidRecallStateError = {
  INVALID_RECALL_STATE: (message = 'No active recall session exists') =>
    new RecallError(message, 'INVALID_RECALL_STATE', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Step 2: Utterance produces no recognizable slots
// ---------------------------------------------------------------------------

export const SlotParsingError = {
  SLOT_PARSING_ERROR: (message = 'Could not extract recognizable slot values from utterance') =>
    new RecallError(message, 'SLOT_PARSING_ERROR', 422, true),
} as const;

// ---------------------------------------------------------------------------
// Step 3 & 4: Slot identifiers do not match schema or constraints fail
// ---------------------------------------------------------------------------

export const SlotValidationError = {
  SLOT_VALIDATION_ERROR: (message = 'Slot identifiers or values do not match question type schema') =>
    new RecallError(message, 'SLOT_VALIDATION_ERROR', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Step 5: State update fails during completion
// ---------------------------------------------------------------------------

export const RecallStateTransitionError = {
  RECALL_STATE_TRANSITION_ERROR: (message = 'Failed to update recall session state during completion') =>
    new RecallError(message, 'RECALL_STATE_TRANSITION_ERROR', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Feedback loop: Retry limit exceeded
// ---------------------------------------------------------------------------

export const IncompleteInformationError = {
  INCOMPLETE_INFORMATION_ERROR: (message = 'Maximum retry limit exceeded — required slots remain unfilled') =>
    new RecallError(message, 'INCOMPLETE_INFORMATION_ERROR', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate — all error factories
// ---------------------------------------------------------------------------

export const RecallErrors = {
  ...InvalidRecallStateError,
  ...SlotParsingError,
  ...SlotValidationError,
  ...RecallStateTransitionError,
  ...IncompleteInformationError,
} as const;
