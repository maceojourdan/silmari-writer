/**
 * OrientErrors - Standardized error definitions for the orient-state-creates-single-story-record path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 295-orient-state-creates-single-story-record
 */

export type OrientErrorCode =
  | 'SYSTEM_PROCESS_CHAIN_NOT_FOUND'
  | 'NO_VALID_EXPERIENCE_SELECTED'
  | 'STORY_RECORD_VALIDATION_FAILED'
  | 'STORY_RECORD_PERSISTENCE_FAILED';

export class OrientError extends Error {
  code: OrientErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: OrientErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'OrientError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const OrientErrors = {
  SystemProcessChainNotFound: (message = 'ORIENT process chain is not registered') =>
    new OrientError(message, 'SYSTEM_PROCESS_CHAIN_NOT_FOUND', 500, false),

  NoValidExperienceSelected: (message = 'No valid experience could be selected') =>
    new OrientError(message, 'NO_VALID_EXPERIENCE_SELECTED', 422, false),

  StoryRecordValidationFailed: (message = 'Story record validation failed') =>
    new OrientError(message, 'STORY_RECORD_VALIDATION_FAILED', 422, false),

  StoryRecordPersistenceFailed: (message = 'Failed to persist story record') =>
    new OrientError(message, 'STORY_RECORD_PERSISTENCE_FAILED', 500, true),
} as const;
