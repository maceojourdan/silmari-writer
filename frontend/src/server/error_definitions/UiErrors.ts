/**
 * UiErrors - Frontend UI error definitions for state, access, component, and data failures.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * Error codes used across RECALL module for:
 * - State detection failures (UI_STATE_NOT_FOUND)
 * - Access control denials (UI_RECALL_ACCESS_DENIED)
 * - Component initialization failures (UI_COMPONENT_INIT_ERROR)
 * - Progress data loading failures (UI_PROGRESS_LOAD_FAILED)
 * - Record button styling failures (UI_RECORD_BUTTON_STYLE_ERROR)
 */

export type UiErrorCode =
  | 'UI_STATE_NOT_FOUND'
  | 'UI_RECALL_ACCESS_DENIED'
  | 'UI_COMPONENT_INIT_ERROR'
  | 'UI_PROGRESS_LOAD_FAILED'
  | 'UI_RECORD_BUTTON_STYLE_ERROR';

export class UiError extends Error {
  code: UiErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: UiErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'UiError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const UiErrors = {
  StateNotFound: (message = 'Application state could not be determined') =>
    new UiError(message, 'UI_STATE_NOT_FOUND', 500, false),

  RecallAccessDenied: (message = 'User is not authorized to access the RECALL interface') =>
    new UiError(message, 'UI_RECALL_ACCESS_DENIED', 403, false),

  ComponentInitError: (message = 'A required UI component failed to initialize') =>
    new UiError(message, 'UI_COMPONENT_INIT_ERROR', 500, false),

  ProgressLoadFailed: (message = 'Failed to load progress data') =>
    new UiError(message, 'UI_PROGRESS_LOAD_FAILED', 500, true),

  RecordButtonStyleError: (message = 'Record button styling failed') =>
    new UiError(message, 'UI_RECORD_BUTTON_STYLE_ERROR', 500, false),
} as const;
