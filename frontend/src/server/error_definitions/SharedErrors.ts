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
  | 'VOICE_CAPTURE_FAILED';

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
} as const;
