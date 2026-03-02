/**
 * SmsErrors - Standardized error definitions for the SMS follow-up path.
 *
 * Covers claim loading, SMS sending, and truth check persistence failures.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 305-followup-sms-for-uncertain-claim
 */

export type SmsErrorCode =
  | 'CLAIM_LOAD_FAILED'
  | 'SMS_SEND_FAILED'
  | 'TRUTH_CHECK_PERSIST_FAILED'
  | 'ANSWER_NOT_FOUND'
  | 'DATABASE_FAILURE'
  | 'PROVIDER_FAILURE'
  | 'PERSISTENCE_FAILURE';

export class SmsError extends Error {
  code: SmsErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: SmsErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'SmsError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 2: Validate claim eligibility — DAO failure
// ---------------------------------------------------------------------------

export const SmsClaimError = {
  CLAIM_LOAD_FAILED: (message = 'Failed to load claim from database') =>
    new SmsError(message, 'CLAIM_LOAD_FAILED', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Step 3: Send follow-up SMS — provider failure
// ---------------------------------------------------------------------------

export const SmsSendError = {
  SMS_SEND_FAILED: (message = 'Failed to send SMS after all retry attempts') =>
    new SmsError(message, 'SMS_SEND_FAILED', 502, true),
} as const;

// ---------------------------------------------------------------------------
// Step 5: Update truth_checks — persistence failure
// ---------------------------------------------------------------------------

export const SmsPersistError = {
  TRUTH_CHECK_PERSIST_FAILED: (message = 'Failed to persist truth check update') =>
    new SmsError(message, 'TRUTH_CHECK_PERSIST_FAILED', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Path 335: trigger-sms-follow-up-on-answer-finalization
// ---------------------------------------------------------------------------

export const SmsFollowUpErrors = {
  ANSWER_NOT_FOUND: (message = 'Answer not found for SMS follow-up') =>
    new SmsError(message, 'ANSWER_NOT_FOUND', 404, false),

  DATABASE_FAILURE: (message = 'Database failure during SMS follow-up') =>
    new SmsError(message, 'DATABASE_FAILURE', 500, true),

  PROVIDER_FAILURE: (message = 'SMS provider failure after all retry attempts') =>
    new SmsError(message, 'PROVIDER_FAILURE', 502, true),

  PERSISTENCE_FAILURE: (message = 'Failed to persist SMS follow-up record') =>
    new SmsError(message, 'PERSISTENCE_FAILURE', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate — all error factories
// ---------------------------------------------------------------------------

export const BackendErrors = {
  ...SmsClaimError,
  ...SmsSendError,
  ...SmsPersistError,
  ...SmsFollowUpErrors,
} as const;
