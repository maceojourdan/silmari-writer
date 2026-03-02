/**
 * FinalizeAnswerErrors - Backend error definitions for the finalize-answer-locks-editing path.
 *
 * Covers answer lookup, eligibility checks, persistence, and serialization errors.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 333-finalize-answer-locks-editing
 */

export type FinalizeAnswerErrorCode =
  | 'ANSWER_NOT_FOUND'
  | 'ANSWER_NOT_COMPLETED'
  | 'ANSWER_ALREADY_FINALIZED'
  | 'UNAUTHORIZED'
  | 'VALIDATION_ERROR'
  | 'SERIALIZATION_ERROR'
  | 'PERSISTENCE_FAILURE';

export class FinalizeAnswerError extends Error {
  code: FinalizeAnswerErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: FinalizeAnswerErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'FinalizeAnswerError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const FinalizeAnswerErrors = {
  AnswerNotFound: (message = 'Answer not found') =>
    new FinalizeAnswerError(message, 'ANSWER_NOT_FOUND', 404, false),

  AnswerNotCompleted: (message = 'Answer is not in COMPLETED status') =>
    new FinalizeAnswerError(message, 'ANSWER_NOT_COMPLETED', 422, false),

  AnswerAlreadyFinalized: (message = 'Answer has already been finalized') =>
    new FinalizeAnswerError(message, 'ANSWER_ALREADY_FINALIZED', 409, false),

  Unauthorized: (message = 'Authentication required') =>
    new FinalizeAnswerError(message, 'UNAUTHORIZED', 401, false),

  ValidationError: (message = 'Request validation failed') =>
    new FinalizeAnswerError(message, 'VALIDATION_ERROR', 400, false),

  SerializationError: (message = 'Failed to serialize finalize response') =>
    new FinalizeAnswerError(message, 'SERIALIZATION_ERROR', 500, false),

  PersistenceFailure: (message = 'Failed to persist finalized answer') =>
    new FinalizeAnswerError(message, 'PERSISTENCE_FAILURE', 500, true),
} as const;
