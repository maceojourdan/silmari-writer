/**
 * VerificationErrors - Standardized error definitions for the
 * claim verification via voice/SMS path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Paths:
 *   - 321-verify-key-claims-via-voice-or-sms
 *   - 323-fail-verification-when-no-contact-method
 */

// ---------------------------------------------------------------------------
// Error codes
// ---------------------------------------------------------------------------

export type VerificationErrorCode =
  | 'CLAIM_ELIGIBILITY_ERROR'
  | 'INVALID_CONTACT'
  | 'DELIVERY_FAILED'
  | 'RETRY_LIMIT_EXCEEDED'
  | 'DATA_ACCESS_ERROR'
  | 'VERIFICATION_STATE_INCONSISTENT'
  | 'CONFIRMATION_FAILED'
  // Path 323: fail-verification-when-no-contact-method
  | 'VERIFICATION_REQUEST_INVALID'
  | 'CLAIMANT_NOT_FOUND'
  | 'INTERNAL_VALIDATION_ERROR'
  | 'VERIFICATION_PERSISTENCE_FAILED'
  | 'DRAFTING_BLOCKED'
  | 'GENERIC_VERIFICATION_FAILURE';

// ---------------------------------------------------------------------------
// Error class
// ---------------------------------------------------------------------------

export class VerificationError extends Error {
  code: VerificationErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: VerificationErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'VerificationError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 1: Detect eligibility — missing categories or malformed data
// ---------------------------------------------------------------------------

export const ClaimEligibilityError = {
  CLAIM_ELIGIBILITY_ERROR: (message = 'Claims are not eligible for verification') =>
    new VerificationError(message, 'CLAIM_ELIGIBILITY_ERROR', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Step 2: Initiate verification — contact / delivery issues
// ---------------------------------------------------------------------------

export const InvalidContactError = {
  INVALID_CONTACT: (message = 'Invalid contact details for verification') =>
    new VerificationError(message, 'INVALID_CONTACT', 422, false),
} as const;

export const DeliveryFailedError = {
  DELIVERY_FAILED: (message = 'Failed to deliver verification request') =>
    new VerificationError(message, 'DELIVERY_FAILED', 502, true),
} as const;

export const RetryLimitExceededError = {
  RETRY_LIMIT_EXCEEDED: (message = 'Verification delivery failed after maximum retries') =>
    new VerificationError(message, 'RETRY_LIMIT_EXCEEDED', 502, false),
} as const;

// ---------------------------------------------------------------------------
// Step 3: Confirmation — partial / ambiguous / expired
// ---------------------------------------------------------------------------

export const ConfirmationFailedError = {
  CONFIRMATION_FAILED: (message = 'Confirmation failed or incomplete') =>
    new VerificationError(message, 'CONFIRMATION_FAILED', 422, true),
} as const;

// ---------------------------------------------------------------------------
// Step 4: Persistence failure
// ---------------------------------------------------------------------------

export const DataAccessError = {
  DATA_ACCESS_ERROR: (message = 'Failed to persist verification status update') =>
    new VerificationError(message, 'DATA_ACCESS_ERROR', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Step 5: Inconsistent verification state
// ---------------------------------------------------------------------------

export const VerificationStateInconsistentError = {
  VERIFICATION_STATE_INCONSISTENT: (
    message = 'Cannot enable drafting due to inconsistent verification state',
  ) =>
    new VerificationError(message, 'VERIFICATION_STATE_INCONSISTENT', 409, false),
} as const;

// ---------------------------------------------------------------------------
// Path 323: fail-verification-when-no-contact-method
// ---------------------------------------------------------------------------

// Step 1: Request validation failure
export const VerificationRequestInvalidError = {
  VERIFICATION_REQUEST_INVALID: (message = 'Verification initiation request is invalid') =>
    new VerificationError(message, 'VERIFICATION_REQUEST_INVALID', 400, false),
} as const;

// Step 2: Claimant not found
export const ClaimantNotFoundError = {
  CLAIMANT_NOT_FOUND: (message = 'Claimant record not found') =>
    new VerificationError(message, 'CLAIMANT_NOT_FOUND', 404, false),
} as const;

// Step 3: Internal validation error (verifier execution fails)
export const InternalValidationError = {
  INTERNAL_VALIDATION_ERROR: (message = 'Internal validation error during contact method check') =>
    new VerificationError(message, 'INTERNAL_VALIDATION_ERROR', 500, false),
} as const;

// Step 4: Persistence failure when recording verification attempt
export const VerificationPersistenceFailedError = {
  VERIFICATION_PERSISTENCE_FAILED: (message = 'Failed to persist verification attempt') =>
    new VerificationError(message, 'VERIFICATION_PERSISTENCE_FAILED', 500, true),
} as const;

// Step 5: Drafting blocked due to failed verification
export const DraftingBlockedError = {
  DRAFTING_BLOCKED: (message = 'Drafting is blocked due to failed verification') =>
    new VerificationError(message, 'DRAFTING_BLOCKED', 409, false),
} as const;

// Step 6: Generic serialization / response failure
export const GenericVerificationFailureError = {
  GENERIC_VERIFICATION_FAILURE: (message = 'An unexpected verification error occurred') =>
    new VerificationError(message, 'GENERIC_VERIFICATION_FAILURE', 500, false),
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate
// ---------------------------------------------------------------------------

export const VerificationErrors = {
  ...ClaimEligibilityError,
  ...InvalidContactError,
  ...DeliveryFailedError,
  ...RetryLimitExceededError,
  ...ConfirmationFailedError,
  ...DataAccessError,
  ...VerificationStateInconsistentError,
  // Path 323
  ...VerificationRequestInvalidError,
  ...ClaimantNotFoundError,
  ...InternalValidationError,
  ...VerificationPersistenceFailedError,
  ...DraftingBlockedError,
  ...GenericVerificationFailureError,
} as const;
