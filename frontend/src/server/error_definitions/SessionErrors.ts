/**
 * SessionErrors - Standardized error definitions for the session initialization path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 294-parse-and-store-session-input-objects
 */

export type SessionErrorCode =
  | 'INVALID_REQUEST'
  | 'PARSE_FAILURE'
  | 'VALIDATION_FAILURE'
  | 'PERSISTENCE_FAILURE';

export class SessionError extends Error {
  code: SessionErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: SessionErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'SessionError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const SessionErrors = {
  InvalidRequest: (message = 'Invalid session initialization request') =>
    new SessionError(message, 'INVALID_REQUEST', 400, false),

  ParseFailure: (message = 'Failed to parse session input') =>
    new SessionError(message, 'PARSE_FAILURE', 422, false),

  ValidationFailure: (message = 'Session input validation failed') =>
    new SessionError(message, 'VALIDATION_FAILURE', 422, false),

  PersistenceFailure: (message = 'Failed to persist session data') =>
    new SessionError(message, 'PERSISTENCE_FAILURE', 500, true),
} as const;
