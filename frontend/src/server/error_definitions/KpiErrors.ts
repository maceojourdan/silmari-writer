/**
 * KpiErrors - Backend error definitions for primary KPI operations.
 *
 * Covers validation, persistence, analytics emission, and domain errors.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 339-record-primary-kpi-analytics-event
 */

export type KpiErrorCode =
  | 'VALIDATION_ERROR'
  | 'UNAUTHORIZED'
  | 'DOMAIN_VALIDATION_ERROR'
  | 'PERSISTENCE_ERROR'
  | 'ANALYTICS_TRANSFORM_ERROR'
  | 'ANALYTICS_EMISSION_ERROR'
  | 'SERIALIZATION_ERROR';

export class KpiError extends Error {
  code: KpiErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: KpiErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'KpiError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const KpiErrors = {
  ValidationError: (message = 'Request validation failed') =>
    new KpiError(message, 'VALIDATION_ERROR', 400, false),

  Unauthorized: (message = 'Authentication required') =>
    new KpiError(message, 'UNAUTHORIZED', 401, false),

  DomainValidationError: (message = 'KPI data failed business rule validation') =>
    new KpiError(message, 'DOMAIN_VALIDATION_ERROR', 422, false),

  PersistenceError: (message = 'Failed to persist primary KPI record') =>
    new KpiError(message, 'PERSISTENCE_ERROR', 500, true),

  AnalyticsTransformError: (message = 'Failed to transform KPI record to analytics payload') =>
    new KpiError(message, 'ANALYTICS_TRANSFORM_ERROR', 500, false),

  AnalyticsEmissionError: (message = 'Failed to emit analytics event after retries') =>
    new KpiError(message, 'ANALYTICS_EMISSION_ERROR', 500, true),

  SerializationError: (message = 'Failed to serialize KPI response') =>
    new KpiError(message, 'SERIALIZATION_ERROR', 500, false),
} as const;
