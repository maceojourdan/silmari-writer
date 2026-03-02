/**
 * BackendErrors - Backend error definitions for the onboarding completion
 * and KPI analytics recording path.
 *
 * Covers validation, eligibility, persistence, KPI, and serialization errors.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

export type BackendErrorCode =
  | 'INVALID_REQUEST'
  | 'UNAUTHORIZED'
  | 'USER_NOT_ELIGIBLE'
  | 'STEP_ALREADY_COMPLETED'
  | 'PERSISTENCE_FAILED'
  | 'KPI_IDENTIFIER_MISSING'
  | 'ANALYTICS_PERSISTENCE_FAILED'
  | 'SERIALIZATION_ERROR';

export class BackendError extends Error {
  code: BackendErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: BackendErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'BackendError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const BackendErrors = {
  InvalidRequest: (message = 'Request validation failed') =>
    new BackendError(message, 'INVALID_REQUEST', 400, false),

  Unauthorized: (message = 'Authentication required') =>
    new BackendError(message, 'UNAUTHORIZED', 401, false),

  UserNotEligible: (message = 'User is not eligible for this onboarding step') =>
    new BackendError(message, 'USER_NOT_ELIGIBLE', 422, false),

  StepAlreadyCompleted: (message = 'Onboarding step has already been completed') =>
    new BackendError(message, 'STEP_ALREADY_COMPLETED', 409, false),

  PersistenceFailed: (message = 'Failed to persist onboarding completion') =>
    new BackendError(message, 'PERSISTENCE_FAILED', 500, true),

  KpiIdentifierMissing: (message = 'Required KPI identifier is missing') =>
    new BackendError(message, 'KPI_IDENTIFIER_MISSING', 500, false),

  AnalyticsPersistenceFailed: (
    message = 'Failed to persist analytics event',
  ) => new BackendError(message, 'ANALYTICS_PERSISTENCE_FAILED', 500, true),

  SerializationError: (message = 'Failed to serialize response') =>
    new BackendError(message, 'SERIALIZATION_ERROR', 500, false),
} as const;
