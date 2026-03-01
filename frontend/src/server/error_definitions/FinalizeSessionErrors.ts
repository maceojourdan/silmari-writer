/**
 * FinalizeSessionErrors - Backend error definitions for the
 * finalize-voice-session-and-persist-storyrecord path.
 *
 * Covers session validation, state transition, and StoryRecord persistence errors.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

export type FinalizeSessionErrorCode =
  | 'SESSION_NOT_FOUND'
  | 'INVALID_SESSION_STATE'
  | 'INCOMPLETE_SESSION'
  | 'SESSION_PERSISTENCE_ERROR'
  | 'STORY_RECORD_PERSISTENCE_ERROR'
  | 'RESPONSE_CONSTRUCTION_ERROR';

export class FinalizeSessionError extends Error {
  code: FinalizeSessionErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: FinalizeSessionErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'FinalizeSessionError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const FinalizeSessionErrors = {
  SessionNotFound: (message = 'Session not found') =>
    new FinalizeSessionError(message, 'SESSION_NOT_FOUND', 404, false),

  InvalidSessionState: (message = 'Session is not in ACTIVE state') =>
    new FinalizeSessionError(message, 'INVALID_SESSION_STATE', 409, false),

  IncompleteSession: (message = 'Session has incomplete required inputs') =>
    new FinalizeSessionError(message, 'INCOMPLETE_SESSION', 422, false),

  SessionPersistenceError: (message = 'Failed to persist session state change') =>
    new FinalizeSessionError(message, 'SESSION_PERSISTENCE_ERROR', 500, true),

  StoryRecordPersistenceError: (message = 'Failed to persist StoryRecord') =>
    new FinalizeSessionError(message, 'STORY_RECORD_PERSISTENCE_ERROR', 500, true),

  ResponseConstructionError: (message = 'Failed to construct finalize response') =>
    new FinalizeSessionError(message, 'RESPONSE_CONSTRUCTION_ERROR', 500, false),
} as const;
