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
  | 'TRUTH_CHECK_PERSIST_FAILED';

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
// Convenience aggregate — all error factories
// ---------------------------------------------------------------------------

export const BackendErrors = {
  ...SmsClaimError,
  ...SmsSendError,
  ...SmsPersistError,
} as const;
