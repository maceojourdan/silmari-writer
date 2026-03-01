/**
 * SlotErrors - Structured error definitions for the re-prompt unfilled
 * required slots path.
 *
 * Provides typed error factories for submission validation, schema errors,
 * workflow guard violations, and slot retrieval failures during the
 * re-prompt loop.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 320-re-prompt-unfilled-required-slots
 */

// ---------------------------------------------------------------------------
// Error codes
// ---------------------------------------------------------------------------

export type SlotErrorCode =
  | 'SLOT_SUBMISSION_INVALID'
  | 'REQUIRED_SLOT_SCHEMA_ERROR'
  | 'WORKFLOW_GUARD_VIOLATION'
  | 'RECOVERABLE_SLOT_RETRIEVAL_ERROR';

// ---------------------------------------------------------------------------
// Base SlotError class
// ---------------------------------------------------------------------------

export class SlotError extends Error {
  code: SlotErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: SlotErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'SlotError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 1: Malformed submission payload
// ---------------------------------------------------------------------------

export const SlotSubmissionInvalidError = {
  SLOT_SUBMISSION_INVALID: (message = 'Slot submission payload is malformed or incomplete') =>
    new SlotError(message, 'SLOT_SUBMISSION_INVALID', 400, false),
} as const;

// ---------------------------------------------------------------------------
// Step 2: Corrupt schema or inconsistent definitions
// ---------------------------------------------------------------------------

export const RequiredSlotSchemaError = {
  REQUIRED_SLOT_SCHEMA_ERROR: (message = 'Required slot schema is corrupt or inconsistent') =>
    new SlotError(message, 'REQUIRED_SLOT_SCHEMA_ERROR', 500, false),
} as const;

// ---------------------------------------------------------------------------
// Step 3: Guard violation — attempted progression with unfilled slots
// ---------------------------------------------------------------------------

export const WorkflowGuardViolationError = {
  WORKFLOW_GUARD_VIOLATION: (message = 'Workflow progression attempted with unfilled required slots') =>
    new SlotError(message, 'WORKFLOW_GUARD_VIOLATION', 409, false),
} as const;

// ---------------------------------------------------------------------------
// Step 4: Recoverable slot retrieval failure
// ---------------------------------------------------------------------------

export const RecoverableSlotRetrievalError = {
  RECOVERABLE_SLOT_RETRIEVAL_ERROR: (message = 'Failed to retrieve missing slot list — displaying generic prompt') =>
    new SlotError(message, 'RECOVERABLE_SLOT_RETRIEVAL_ERROR', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate — all error factories
// ---------------------------------------------------------------------------

export const SlotErrors = {
  ...SlotSubmissionInvalidError,
  ...RequiredSlotSchemaError,
  ...WorkflowGuardViolationError,
  ...RecoverableSlotRetrievalError,
} as const;
