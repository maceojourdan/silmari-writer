/**
 * ApprovalErrors - Standardized error definitions for the content approval path.
 *
 * Covers validation, eligibility, persistence, and request errors
 * for the 329-approve-reviewed-content-and-advance-workflow path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 */

export type ApprovalErrorCode =
  | 'INVALID_REQUEST'
  | 'UNAUTHORIZED'
  | 'CONTENT_NOT_FOUND'
  | 'CONTENT_NOT_ELIGIBLE'
  | 'PERSISTENCE_ERROR';

export class ApprovalError extends Error {
  code: ApprovalErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: ApprovalErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'ApprovalError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Request validation errors — Step 2: endpoint validation
// ---------------------------------------------------------------------------

export const ApprovalRequestError = {
  INVALID_REQUEST: (message = 'Invalid approval request') =>
    new ApprovalError(message, 'INVALID_REQUEST', 400, false),

  UNAUTHORIZED: (message = 'Unauthorized approval request') =>
    new ApprovalError(message, 'UNAUTHORIZED', 401, false),
} as const;

// ---------------------------------------------------------------------------
// Eligibility errors — Step 3: business rule validation
// ---------------------------------------------------------------------------

export const ApprovalEligibilityError = {
  CONTENT_NOT_FOUND: (message = 'Content not found') =>
    new ApprovalError(message, 'CONTENT_NOT_FOUND', 404, false),

  CONTENT_NOT_ELIGIBLE: (message = 'Content is not eligible for approval') =>
    new ApprovalError(message, 'CONTENT_NOT_ELIGIBLE', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Persistence errors — Step 4: database persistence
// ---------------------------------------------------------------------------

export const ApprovalPersistenceError = {
  PERSISTENCE_ERROR: (message = 'Failed to persist content approval') =>
    new ApprovalError(message, 'PERSISTENCE_ERROR', 500, true),
} as const;
