/**
 * FinalizeWithoutSmsErrors - Error definitions for the finalize-answer-without-sms-follow-up path.
 *
 * Covers answer lookup, eligibility verification, SMS guard, and persistence failures.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

export type FinalizeWithoutSmsErrorCode =
  | 'ANSWER_NOT_FOUND'
  | 'PERSISTENCE_ERROR'
  | 'INVALID_FINALIZE_STATE'
  | 'FINALIZE_PERSISTENCE_ERROR'
  | 'INADVERTENT_SMS_DISPATCH';

export class FinalizeWithoutSmsError extends Error {
  code: FinalizeWithoutSmsErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: FinalizeWithoutSmsErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'FinalizeWithoutSmsError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const FinalizeWithoutSmsErrors = {
  AnswerNotFound: (message = 'Answer not found') =>
    new FinalizeWithoutSmsError(message, 'ANSWER_NOT_FOUND', 404, false),

  PersistenceError: (message = 'Failed to retrieve data from persistence') =>
    new FinalizeWithoutSmsError(message, 'PERSISTENCE_ERROR', 500, true),

  InvalidFinalizeState: (message = 'Answer is not in FINALIZED state') =>
    new FinalizeWithoutSmsError(message, 'INVALID_FINALIZE_STATE', 422, false),

  FinalizePersistenceError: (message = 'Failed to persist finalization metadata') =>
    new FinalizeWithoutSmsError(message, 'FINALIZE_PERSISTENCE_ERROR', 500, true),

  InadvertentSmsDispatch: (message = 'SMS dispatch was inadvertently triggered despite ineligibility') =>
    new FinalizeWithoutSmsError(message, 'INADVERTENT_SMS_DISPATCH', 500, false),
} as const;
