/**
 * ConfirmStoryErrors - Standardized error definitions for the confirm-aligned-story-selection path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 313-confirm-aligned-story-selection
 */

export type ConfirmStoryErrorCode =
  | 'DATA_NOT_FOUND'
  | 'STORY_NOT_FOUND'
  | 'STORY_ALREADY_CONFIRMED'
  | 'STORY_NOT_ALIGNED'
  | 'INVALID_REQUEST'
  | 'PERSISTENCE_FAILURE'
  | 'CONFIRMATION_FAILED';

export class ConfirmStoryError extends Error {
  code: ConfirmStoryErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: ConfirmStoryErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'ConfirmStoryError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const ConfirmStoryErrors = {
  DataNotFound: (message = 'Question, job requirements, or stories could not be retrieved') =>
    new ConfirmStoryError(message, 'DATA_NOT_FOUND', 404, true),

  StoryNotFound: (message = 'Selected story not found') =>
    new ConfirmStoryError(message, 'STORY_NOT_FOUND', 404, false),

  StoryAlreadyConfirmed: (message = 'Story has already been confirmed for this question') =>
    new ConfirmStoryError(message, 'STORY_ALREADY_CONFIRMED', 409, false),

  StoryNotAligned: (message = 'Selected story does not align with the current question and job requirements') =>
    new ConfirmStoryError(message, 'STORY_NOT_ALIGNED', 422, false),

  InvalidRequest: (message = 'Invalid confirmation request') =>
    new ConfirmStoryError(message, 'INVALID_REQUEST', 400, false),

  PersistenceFailure: (message = 'Failed to persist story confirmation') =>
    new ConfirmStoryError(message, 'PERSISTENCE_FAILURE', 500, true),

  ConfirmationFailed: (message = 'Story confirmation failed') =>
    new ConfirmStoryError(message, 'CONFIRMATION_FAILED', 500, false),
} as const;
