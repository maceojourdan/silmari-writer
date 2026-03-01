/**
 * StoryErrors - Standardized error definitions for the approve-story path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

export type StoryErrorCode =
  | 'UNAUTHORIZED'
  | 'VALIDATION_ERROR'
  | 'RELATED_ENTITY_NOT_FOUND'
  | 'PERSISTENCE_FAILED';

export class StoryError extends Error {
  code: StoryErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: StoryErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'StoryError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const StoryErrors = {
  UNAUTHORIZED: (message = 'Authentication required') =>
    new StoryError(message, 'UNAUTHORIZED', 401, false),

  VALIDATION_ERROR: (message = 'Invalid request payload') =>
    new StoryError(message, 'VALIDATION_ERROR', 400, false),

  RELATED_ENTITY_NOT_FOUND: (entity: string) =>
    new StoryError(
      `Related entity not found: ${entity}`,
      'RELATED_ENTITY_NOT_FOUND',
      404,
      false,
    ),

  PERSISTENCE_FAILED: (message = 'Failed to persist story record') =>
    new StoryError(message, 'PERSISTENCE_FAILED', 500, true),
} as const;
