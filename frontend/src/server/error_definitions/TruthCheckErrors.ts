/**
 * TruthCheckErrors - Standardized error definitions for the
 * truth check confirmation path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 297-confirm-metric-claim-truth-check
 */

export type TruthCheckErrorCode =
  | 'TRUTH_CHECK_VALIDATION_ERROR'
  | 'TRUTH_CHECK_PERSISTENCE_ERROR';

export class TruthCheckError extends Error {
  code: TruthCheckErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: TruthCheckErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'TruthCheckError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const TruthCheckErrors = {
  VALIDATION_ERROR: (message = 'Invalid truth check data') =>
    new TruthCheckError(message, 'TRUTH_CHECK_VALIDATION_ERROR', 400, false),

  PERSISTENCE_ERROR: (message = 'Failed to persist truth check entry') =>
    new TruthCheckError(message, 'TRUTH_CHECK_PERSISTENCE_ERROR', 500, true),
} as const;
