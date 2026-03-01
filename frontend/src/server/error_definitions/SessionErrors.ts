/**
 * SessionErrors - Standardized error definitions for session paths.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Paths:
 *   - 294-parse-and-store-session-input-objects
 *   - 306-initiate-voice-assisted-answer-session
 *   - 307-process-voice-input-and-progress-session
 *   - 309-reject-modifications-to-finalized-session
 *   - 310-initialize-new-session-with-provided-objects
 *   - 311-reject-duplicate-session-initialization
 *   - 312-reject-session-initialization-when-required-objects-missing-or-invalid
 */

export type SessionErrorCode =
  | 'INVALID_REQUEST'
  | 'INVALID_REQUEST_FORMAT'
  | 'PARSE_FAILURE'
  | 'VALIDATION_FAILURE'
  | 'MISSING_REQUIRED_OBJECT'
  | 'PERSISTENCE_FAILURE'
  | 'INTERNAL_PERSISTENCE_VIOLATION'
  | 'SERVICE_ERROR'
  | 'SERVICE_INVOCATION_FAILED'
  | 'SESSION_PERSISTENCE_ERROR'
  | 'STORY_PERSISTENCE_ERROR'
  | 'INVALID_STATE'
  | 'INVALID_PAYLOAD'
  | 'INVALID_TRANSITION'
  | 'PERSISTENCE_FAILED'
  | 'SESSION_NOT_FOUND'
  | 'SESSION_ALREADY_FINALIZED'
  | 'SESSION_ALREADY_ACTIVE'
  | 'CONFLICT_GENERIC'
  | 'GENERIC_USER_ERROR';

export class SessionError extends Error {
  code: SessionErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: SessionErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'SessionError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const SessionErrors = {
  InvalidRequest: (message = 'Invalid session initialization request') =>
    new SessionError(message, 'INVALID_REQUEST', 400, false),

  // Path 312: reject-session-initialization-when-required-objects-missing-or-invalid
  InvalidRequestFormat: (message = 'Request payload could not be parsed') =>
    new SessionError(message, 'INVALID_REQUEST_FORMAT', 400, false),

  ParseFailure: (message = 'Failed to parse session input') =>
    new SessionError(message, 'PARSE_FAILURE', 422, false),

  ValidationFailure: (message = 'Session input validation failed') =>
    new SessionError(message, 'VALIDATION_FAILURE', 422, false),

  // Path 312: Missing or invalid required domain object
  MissingRequiredObject: (message = 'One or more required objects are missing or invalid') =>
    new SessionError(message, 'MISSING_REQUIRED_OBJECT', 400, false),

  PersistenceFailure: (message = 'Failed to persist session data') =>
    new SessionError(message, 'PERSISTENCE_FAILURE', 500, true),

  // Path 312: Defense-in-depth guard against persistence after validation failure
  InternalPersistenceViolation: (message = 'Attempted to persist session despite validation errors') =>
    new SessionError(message, 'INTERNAL_PERSISTENCE_VIOLATION', 500, false),

  // Path 310: initialize-new-session-with-provided-objects
  ServiceError: (message = 'Service-level error during session initialization') =>
    new SessionError(message, 'SERVICE_ERROR', 500, false),

  // Path 312: Handler-to-service contract violation
  ServiceInvocationFailed: (message = 'Failed to invoke session initialization service') =>
    new SessionError(message, 'SERVICE_INVOCATION_FAILED', 500, false),

  // Path 306: initiate-voice-assisted-answer-session
  SessionPersistenceError: (message = 'Failed to persist answer session') =>
    new SessionError(message, 'SESSION_PERSISTENCE_ERROR', 500, true),

  StoryPersistenceError: (message = 'Failed to persist story record') =>
    new SessionError(message, 'STORY_PERSISTENCE_ERROR', 500, true),

  // Path 307: process-voice-input-and-progress-session
  InvalidState: (message = 'Session is not in a valid state for this operation') =>
    new SessionError(message, 'INVALID_STATE', 409, false),

  InvalidPayload: (message = 'Voice response payload is invalid') =>
    new SessionError(message, 'INVALID_PAYLOAD', 400, false),

  InvalidTransition: (message = 'Invalid session state transition') =>
    new SessionError(message, 'INVALID_TRANSITION', 409, false),

  PersistenceFailed: (message = 'Failed to persist session progression') =>
    new SessionError(message, 'PERSISTENCE_FAILED', 500, true),

  // Path 309: reject-modifications-to-finalized-session
  NotFound: (message = 'Session not found') =>
    new SessionError(message, 'SESSION_NOT_FOUND', 404, false),

  SessionAlreadyFinalized: (message = 'Session is already finalized and cannot be modified') =>
    new SessionError(message, 'SESSION_ALREADY_FINALIZED', 409, false),

  // Path 311: reject-duplicate-session-initialization
  SessionAlreadyActive: (message = 'A session is already active. Please finalize or end the current session before starting a new one.') =>
    new SessionError(message, 'SESSION_ALREADY_ACTIVE', 409, false),

  ConflictGeneric: (message = 'A conflict occurred while processing the session modification') =>
    new SessionError(message, 'CONFLICT_GENERIC', 409, false),

  // Path 312: Fallback user-safe error when error mapping fails
  GenericUserError: (message = 'An error occurred during session initialization') =>
    new SessionError(message, 'GENERIC_USER_ERROR', 500, false),
} as const;
