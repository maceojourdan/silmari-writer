/**
 * FinalizeErrors - Backend error definitions for the finalize-approved-draft path.
 *
 * Covers draft validation, state checks, persistence, and transformation errors.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

export type FinalizeErrorCode =
  | 'DRAFT_NOT_FOUND'
  | 'INVALID_DRAFT_STATE'
  | 'PERSISTENCE_FAILURE'
  | 'TRANSFORMATION_FAILURE'
  | 'RESPONSE_CONSTRUCTION_FAILURE';

export class FinalizeError extends Error {
  code: FinalizeErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: FinalizeErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'FinalizeError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const FinalizeErrors = {
  DraftNotFound: (message = 'Draft not found') =>
    new FinalizeError(message, 'DRAFT_NOT_FOUND', 404, false),

  InvalidDraftState: (message = 'Draft is not in APPROVED state') =>
    new FinalizeError(message, 'INVALID_DRAFT_STATE', 422, false),

  PersistenceFailure: (message = 'Failed to persist finalized draft') =>
    new FinalizeError(message, 'PERSISTENCE_FAILURE', 500, true),

  TransformationFailure: (message = 'Failed to transform draft to export artifact') =>
    new FinalizeError(message, 'TRANSFORMATION_FAILURE', 500, false),

  ResponseConstructionFailure: (message = 'Failed to construct finalize response') =>
    new FinalizeError(message, 'RESPONSE_CONSTRUCTION_FAILURE', 500, false),
} as const;
