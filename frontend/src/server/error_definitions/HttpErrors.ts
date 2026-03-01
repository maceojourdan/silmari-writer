/**
 * HttpErrors - Shared HTTP error definitions for authorization, validation,
 * and internal errors across all API endpoints.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 306-initiate-voice-assisted-answer-session
 */

export type HttpErrorCode = 'AUTHORIZATION_ERROR' | 'VALIDATION_ERROR' | 'INTERNAL_ERROR';

export class HttpError extends Error {
  code: HttpErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: HttpErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'HttpError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const HttpErrors = {
  authorization: (message = 'Authentication required') =>
    new HttpError(message, 'AUTHORIZATION_ERROR', 401, false),

  validation: (message = 'Invalid request payload') =>
    new HttpError(message, 'VALIDATION_ERROR', 400, false),

  internal: (message = 'An unexpected internal error occurred') =>
    new HttpError(message, 'INTERNAL_ERROR', 500, false),
} as const;
