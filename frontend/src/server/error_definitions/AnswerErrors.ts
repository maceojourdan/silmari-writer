/**
 * AnswerErrors - Backend error definitions for answer operations.
 *
 * Covers answer lookup, finalized/locked state validation, persistence,
 * and authorization errors.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Paths:
 *   - 334-export-or-copy-finalized-answer
 *   - 337-prevent-edit-of-locked-answer
 */

export type AnswerErrorCode =
  | 'ANSWER_NOT_FOUND'
  | 'ANSWER_NOT_LOCKED'
  | 'LOCKED_ANSWER_MODIFICATION_FORBIDDEN'
  | 'PERSISTENCE_ERROR'
  | 'UNAUTHORIZED'
  | 'VALIDATION_ERROR'
  | 'SERIALIZATION_ERROR';

export class AnswerError extends Error {
  code: AnswerErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: AnswerErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'AnswerError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const AnswerErrors = {
  AnswerNotFound: (message = 'Answer not found') =>
    new AnswerError(message, 'ANSWER_NOT_FOUND', 404, false),

  AnswerNotLocked: (message = 'Answer is not finalized and locked') =>
    new AnswerError(message, 'ANSWER_NOT_LOCKED', 422, false),

  // Path 337: prevent-edit-of-locked-answer
  LockedAnswerModificationForbidden: (message = 'This answer has been finalized and cannot be modified.') =>
    new AnswerError(message, 'LOCKED_ANSWER_MODIFICATION_FORBIDDEN', 403, false),

  PersistenceError: (message = 'Failed to persist answer changes') =>
    new AnswerError(message, 'PERSISTENCE_ERROR', 500, true),

  Unauthorized: (message = 'Authentication required') =>
    new AnswerError(message, 'UNAUTHORIZED', 401, false),

  ValidationError: (message = 'Request validation failed') =>
    new AnswerError(message, 'VALIDATION_ERROR', 400, false),

  SerializationError: (message = 'Failed to serialize answer response') =>
    new AnswerError(message, 'SERIALIZATION_ERROR', 500, false),
} as const;
