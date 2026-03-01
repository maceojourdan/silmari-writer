/**
 * DisputeErrors - Standardized error definitions for the
 * disputed claims and block drafting path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

// ---------------------------------------------------------------------------
// Error codes
// ---------------------------------------------------------------------------

export type DisputeErrorCode =
  | 'MALFORMED_WEBHOOK'
  | 'VERIFICATION_REQUEST_NOT_FOUND'
  | 'SERVICE_INVOCATION_FAILED'
  | 'CLAIM_NOT_FOUND'
  | 'PERSISTENCE_ERROR'
  | 'INVALID_STATE_TRANSITION';

// ---------------------------------------------------------------------------
// Error class
// ---------------------------------------------------------------------------

export class DisputeError extends Error {
  code: DisputeErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: DisputeErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'DisputeError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 1: Receive SMS dispute — malformed / no active verification
// ---------------------------------------------------------------------------

export const MalformedWebhookError = {
  MALFORMED_WEBHOOK: (message = 'Webhook payload is malformed or missing required fields') =>
    new DisputeError(message, 'MALFORMED_WEBHOOK', 400, false),
} as const;

export const VerificationRequestNotFoundError = {
  VERIFICATION_REQUEST_NOT_FOUND: (message = 'No active verification request found for this token') =>
    new DisputeError(message, 'VERIFICATION_REQUEST_NOT_FOUND', 404, false),
} as const;

// ---------------------------------------------------------------------------
// Step 2: Handler-to-service mapping failure
// ---------------------------------------------------------------------------

export const ServiceInvocationFailedError = {
  SERVICE_INVOCATION_FAILED: (message = 'Failed to invoke dispute handling service') =>
    new DisputeError(message, 'SERVICE_INVOCATION_FAILED', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Step 3: Missing claim or DAO update failure
// ---------------------------------------------------------------------------

export const ClaimNotFoundError = {
  CLAIM_NOT_FOUND: (message = 'Disputed claim not found') =>
    new DisputeError(message, 'CLAIM_NOT_FOUND', 404, false),
} as const;

export const DisputePersistenceError = {
  PERSISTENCE_ERROR: (message = 'Failed to persist disputed claim status update') =>
    new DisputeError(message, 'PERSISTENCE_ERROR', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Step 4: Invalid state transition for drafting block
// ---------------------------------------------------------------------------

export const InvalidStateTransitionError = {
  INVALID_STATE_TRANSITION: (message = 'Cannot block drafting from current state') =>
    new DisputeError(message, 'INVALID_STATE_TRANSITION', 409, false),
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate — all error factories
// ---------------------------------------------------------------------------

export const DisputeErrors = {
  ...MalformedWebhookError,
  ...VerificationRequestNotFoundError,
  ...ServiceInvocationFailedError,
  ...ClaimNotFoundError,
  ...DisputePersistenceError,
  ...InvalidStateTransitionError,
} as const;
