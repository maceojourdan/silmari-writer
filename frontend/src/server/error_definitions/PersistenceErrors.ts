/**
 * PersistenceErrors - Backend error definitions for database persistence failures.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

export type PersistenceErrorCode = 'PERSISTENCE_ERROR';

export class PersistenceError extends Error {
  code: PersistenceErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: PersistenceErrorCode = 'PERSISTENCE_ERROR',
    statusCode: number = 500,
    retryable: boolean = true,
  ) {
    super(message);
    this.name = 'PersistenceError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const PersistenceErrors = {
  UpdateFailed: (message = 'Failed to update session state in database') =>
    new PersistenceError(message, 'PERSISTENCE_ERROR', 500, true),
} as const;
