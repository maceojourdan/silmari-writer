/**
 * BehavioralQuestionErrors - Standardized error definitions for the
 * behavioral question evaluation and state transition path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 */

export type BehavioralQuestionErrorCode =
  | 'MINIMUM_SLOTS_NOT_MET'
  | 'VALIDATION_ERROR'
  | 'PERSISTENCE_FAILED';

export class BehavioralQuestionError extends Error {
  code: BehavioralQuestionErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: BehavioralQuestionErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'BehavioralQuestionError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const BehavioralQuestionErrors = {
  MINIMUM_SLOTS_NOT_MET: (message = 'Minimum slot requirements not met') =>
    new BehavioralQuestionError(message, 'MINIMUM_SLOTS_NOT_MET', 422, false),

  VALIDATION_ERROR: (message = 'Invalid behavioral question data') =>
    new BehavioralQuestionError(message, 'VALIDATION_ERROR', 400, false),

  PERSISTENCE_FAILED: (message = 'Failed to persist behavioral question state') =>
    new BehavioralQuestionError(message, 'PERSISTENCE_FAILED', 500, true),
} as const;
