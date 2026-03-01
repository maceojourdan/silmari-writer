/**
 * DomainErrors - Standardized error definitions for domain-level
 * failures including persistence, integrity, concurrency, and validation.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 */

// ---------------------------------------------------------------------------
// Error codes
// ---------------------------------------------------------------------------

export type DomainErrorCode =
  | 'PERSISTENCE_ERROR'
  | 'DOMAIN_INTEGRITY_ERROR'
  | 'CONCURRENCY_CONFLICT_ERROR'
  | 'VALIDATION_ERROR'
  | 'CONFIG_LOAD_ERROR'
  | 'CLAIM_STATUS_LOAD_ERROR';

// ---------------------------------------------------------------------------
// Error class
// ---------------------------------------------------------------------------

export class DomainError extends Error {
  code: DomainErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: DomainErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'DomainError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Persistence errors — data access layer failures
// ---------------------------------------------------------------------------

export const PersistenceError = {
  PERSISTENCE_ERROR: (message = 'Failed to persist data') =>
    new DomainError(message, 'PERSISTENCE_ERROR', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Domain integrity errors — missing required entities
// ---------------------------------------------------------------------------

export const DomainIntegrityError = {
  DOMAIN_INTEGRITY_ERROR: (message = 'Domain entity is missing or invalid') =>
    new DomainError(message, 'DOMAIN_INTEGRITY_ERROR', 404, false),
} as const;

// ---------------------------------------------------------------------------
// Concurrency conflict — concurrent modifications detected
// ---------------------------------------------------------------------------

export const ConcurrencyConflictError = {
  CONCURRENCY_CONFLICT_ERROR: (message = 'Concurrent modification detected') =>
    new DomainError(message, 'CONCURRENCY_CONFLICT_ERROR', 409, false),
} as const;

// ---------------------------------------------------------------------------
// Validation error — business rule validation failure
// ---------------------------------------------------------------------------

export const ValidationError = {
  VALIDATION_ERROR: (message = 'Business rule validation failed') =>
    new DomainError(message, 'VALIDATION_ERROR', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Config load error — configuration loading failure
// ---------------------------------------------------------------------------

export const ConfigLoadError = {
  CONFIG_LOAD_ERROR: (message = 'Failed to load configuration') =>
    new DomainError(message, 'CONFIG_LOAD_ERROR', 500, false),
} as const;

// ---------------------------------------------------------------------------
// Claim status load error — endpoint-specific load failure
// ---------------------------------------------------------------------------

export const ClaimStatusLoadError = {
  CLAIM_STATUS_LOAD_ERROR: (message = 'Failed to load claim status') =>
    new DomainError(message, 'CLAIM_STATUS_LOAD_ERROR', 500, true),
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate
// ---------------------------------------------------------------------------

export const DomainErrors = {
  ...PersistenceError,
  ...DomainIntegrityError,
  ...ConcurrencyConflictError,
  ...ValidationError,
  ...ConfigLoadError,
  ...ClaimStatusLoadError,
} as const;
