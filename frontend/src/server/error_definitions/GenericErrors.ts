/**
 * GenericErrors - Cross-layer error definitions for generic/unexpected failures.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 294-parse-and-store-session-input-objects
 */

export type GenericErrorCode = 'INTERNAL_ERROR' | 'UNKNOWN_ERROR';

export class GenericError extends Error {
  code: GenericErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: GenericErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'GenericError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const GenericErrors = {
  InternalError: (message = 'An unexpected internal error occurred') =>
    new GenericError(message, 'INTERNAL_ERROR', 500, false),

  UnknownError: (message = 'An unknown error occurred') =>
    new GenericError(message, 'UNKNOWN_ERROR', 500, false),
} as const;
