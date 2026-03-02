/**
 * SharedErrors - Cross-layer error definitions for network and shared failures.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Paths:
 *   - 296-transition-to-verify-when-minimum-slots-filled
 *   - 307-process-voice-input-and-progress-session
 *   - 308-finalize-voice-session-and-persist-storyrecord
 *   - 325-generate-draft-from-confirmed-claims
 *   - 327-prevent-draft-generation-without-confirmed-claims
 *   - 330-edit-content-by-voice-from-review-screen
 *   - 333-finalize-answer-locks-editing
 *   - 334-export-or-copy-finalized-answer
 *   - 335-trigger-sms-follow-up-on-answer-finalization
 */

export type SharedErrorCode =
  | 'NETWORK_ERROR'
  | 'TIMEOUT_ERROR'
  | 'MALFORMED_REQUEST'
  | 'REQUEST_VALIDATION_ERROR'
  | 'UNAUTHORIZED'
  | 'NO_ACTIVE_SESSION'
  | 'DOMAIN_ERROR'
  | 'TRANSFORMATION_ERROR'
  | 'VOICE_CAPTURE_FAILED'
  | 'ANSWER_ALREADY_FINALIZED'
  | 'ANSWER_NOT_FINALIZED'
  | 'UNSUPPORTED_EXPORT_FORMAT'
  | 'EXPORT_FAILED'
  | 'MISSING_PHONE_NUMBER'
  | 'SMS_TOO_LONG';

export class SharedError extends Error {
  code: SharedErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: SharedErrorCode,
    statusCode: number = 500,
    retryable: boolean = true,
  ) {
    super(message);
    this.name = 'SharedError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const SharedErrors = {
  NetworkError: (message = 'A network error occurred') =>
    new SharedError(message, 'NETWORK_ERROR', 503, true),

  TimeoutError: (message = 'The request timed out') =>
    new SharedError(message, 'TIMEOUT_ERROR', 504, true),

  MalformedRequest: (message = 'The request is malformed') =>
    new SharedError(message, 'MALFORMED_REQUEST', 400, false),

  // Path 307: process-voice-input-and-progress-session
  Unauthorized: (message = 'Authentication required') =>
    new SharedError(message, 'UNAUTHORIZED', 401, false),

  NoActiveSession: (message = 'No active session found') =>
    new SharedError(message, 'NO_ACTIVE_SESSION', 404, false),

  DomainError: (message = 'A domain error occurred') =>
    new SharedError(message, 'DOMAIN_ERROR', 422, false),

  // Path 308: finalize-voice-session-and-persist-storyrecord
  RequestValidationError: (message = 'Request validation failed') =>
    new SharedError(message, 'REQUEST_VALIDATION_ERROR', 400, false),

  // Path 325: generate-draft-from-confirmed-claims
  TransformationError: (message = 'Structural transformation failed') =>
    new SharedError(message, 'TRANSFORMATION_ERROR', 422, false),

  // Path 330: edit-content-by-voice-from-review-screen
  VoiceCaptureFailed: (message = 'Voice capture or transcription failed') =>
    new SharedError(message, 'VOICE_CAPTURE_FAILED', 422, true),

  // Path 333: finalize-answer-locks-editing
  AnswerAlreadyFinalized: (message = 'This answer has already been finalized and cannot be edited') =>
    new SharedError(message, 'ANSWER_ALREADY_FINALIZED', 409, false),

  // Path 334: export-or-copy-finalized-answer
  AnswerNotFinalized: (message = 'Answer must be finalized and locked before export or copy') =>
    new SharedError(message, 'ANSWER_NOT_FINALIZED', 422, false),

  UnsupportedExportFormat: (message = 'The requested export format is not supported') =>
    new SharedError(message, 'UNSUPPORTED_EXPORT_FORMAT', 422, false),

  ExportFailed: (message = 'Export or clipboard copy operation failed') =>
    new SharedError(message, 'EXPORT_FAILED', 500, true),

  // Path 335: trigger-sms-follow-up-on-answer-finalization
  MissingPhoneNumber: (message = 'Phone number is missing or invalid for SMS follow-up') =>
    new SharedError(message, 'MISSING_PHONE_NUMBER', 422, false),

  SmsTooLong: (message = 'SMS message exceeds maximum allowed length of 160 characters') =>
    new SharedError(message, 'SMS_TOO_LONG', 422, false),
} as const;
