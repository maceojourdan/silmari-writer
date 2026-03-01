/**
 * MetricsErrors - Standardized error definitions for the session metrics pipeline.
 *
 * Covers identifier validation, session retrieval, metrics computation,
 * persistence, and pipeline operational errors.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 301-store-session-metrics-on-pipeline-run
 */

export type MetricsErrorCode =
  | 'INVALID_SESSION_IDENTIFIER'
  | 'SESSION_NOT_FOUND'
  | 'SESSION_NOT_COMPLETED'
  | 'INVALID_METRICS_INPUT'
  | 'METRICS_PERSISTENCE_ERROR'
  | 'METRICS_PIPELINE_OPERATIONAL_ERROR';

export class MetricsError extends Error {
  code: MetricsErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: MetricsErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'MetricsError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 1: Trigger validation errors
// ---------------------------------------------------------------------------

export const InvalidSessionIdentifierError = (
  message = 'Session identifier is missing or malformed',
) => new MetricsError(message, 'INVALID_SESSION_IDENTIFIER', 400, false);

// ---------------------------------------------------------------------------
// Step 2: Session data retrieval errors
// ---------------------------------------------------------------------------

export const SessionNotFoundError = (
  message = 'Session not found',
) => new MetricsError(message, 'SESSION_NOT_FOUND', 404, false);

export const SessionNotCompletedError = (
  message = 'Session is not in FINALIZED state',
) => new MetricsError(message, 'SESSION_NOT_COMPLETED', 422, false);

// ---------------------------------------------------------------------------
// Step 3: Metrics computation errors
// ---------------------------------------------------------------------------

export const InvalidMetricsInputError = (
  message = 'Required data fields are missing or invalid for metrics computation',
) => new MetricsError(message, 'INVALID_METRICS_INPUT', 422, false);

// ---------------------------------------------------------------------------
// Step 4: Persistence errors
// ---------------------------------------------------------------------------

export const MetricsPersistenceError = (
  message = 'Failed to persist session metrics',
) => new MetricsError(message, 'METRICS_PERSISTENCE_ERROR', 500, true);

// ---------------------------------------------------------------------------
// Step 5: Pipeline operational errors
// ---------------------------------------------------------------------------

export const MetricsPipelineOperationalError = (
  message = 'Failed to record pipeline success status',
) => new MetricsError(message, 'METRICS_PIPELINE_OPERATIONAL_ERROR', 500, true);
