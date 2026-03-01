/**
 * DraftErrors - Standardized error definitions for the draft-state path.
 *
 * Covers state validation, data access, validation, service, and API errors
 * for the draft-state-filters-unconfirmed-hard-claims-and-records-claims-used path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Paths:
 *   - 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 *   - 325-generate-draft-from-confirmed-claims
 */

export type DraftErrorCode =
  | 'STORY_NOT_FOUND'
  | 'INVALID_STATE'
  | 'RETRIEVAL_FAILED'
  | 'MALFORMED_TRUTH_CHECKS'
  | 'INVALID_TRUTH_CHECK'
  | 'GENERATION_FAILED'
  | 'PERSISTENCE_FAILED'
  | 'RESPONSE_TRANSFORM_FAILED'
  | 'CLAIM_SET_NOT_FOUND'
  | 'NO_CONFIRMED_CLAIMS'
  | 'INVALID_PARAMETERS';

export class DraftError extends Error {
  code: DraftErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: DraftErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'DraftError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// DraftStateError — Step 1: trigger validation
// ---------------------------------------------------------------------------

export const DraftStateError = {
  STORY_NOT_FOUND: (message = 'StoryRecord not found') =>
    new DraftError(message, 'STORY_NOT_FOUND', 404, false),

  INVALID_STATE: (message = 'StoryRecord is not in DRAFT state') =>
    new DraftError(message, 'INVALID_STATE', 422, false),
} as const;

// ---------------------------------------------------------------------------
// DraftDataAccessError — Steps 2 & 5: retrieval and persistence
// ---------------------------------------------------------------------------

export const DraftDataAccessError = {
  RETRIEVAL_FAILED: (message = 'Failed to retrieve StoryRecord') =>
    new DraftError(message, 'RETRIEVAL_FAILED', 500, true),

  PERSISTENCE_FAILED: (message = 'Failed to persist draft update') =>
    new DraftError(message, 'PERSISTENCE_FAILED', 500, true),
} as const;

// ---------------------------------------------------------------------------
// DraftValidationError — Steps 2 & 3: structural validation
// ---------------------------------------------------------------------------

export const DraftValidationError = {
  MALFORMED_TRUTH_CHECKS: (message = 'Truth checks data is malformed') =>
    new DraftError(message, 'MALFORMED_TRUTH_CHECKS', 422, false),

  INVALID_TRUTH_CHECK: (message = 'Invalid truth check structure') =>
    new DraftError(message, 'INVALID_TRUTH_CHECK', 422, false),
} as const;

// ---------------------------------------------------------------------------
// DraftServiceError — Step 4: draft generation
// ---------------------------------------------------------------------------

export const DraftServiceError = {
  GENERATION_FAILED: (message = 'Draft generation failed') =>
    new DraftError(message, 'GENERATION_FAILED', 500, true),
} as const;

// ---------------------------------------------------------------------------
// DraftApiError — Step 6: response transformation
// ---------------------------------------------------------------------------

export const DraftApiError = {
  RESPONSE_TRANSFORM_FAILED: (message = 'Failed to transform draft response') =>
    new DraftError(message, 'RESPONSE_TRANSFORM_FAILED', 500, false),
} as const;

// ---------------------------------------------------------------------------
// Path 325: generate-draft-from-confirmed-claims
// ---------------------------------------------------------------------------

/**
 * DraftGenerationError — errors specific to draft generation from confirmed claims.
 */
export const DraftGenerationError = {
  CLAIM_SET_NOT_FOUND: (message = 'Claim set not found') =>
    new DraftError(message, 'CLAIM_SET_NOT_FOUND', 404, false),

  NO_CONFIRMED_CLAIMS: (message = 'No confirmed claims found in claim set') =>
    new DraftError(message, 'NO_CONFIRMED_CLAIMS', 422, false),

  INVALID_PARAMETERS: (message = 'Invalid parameters for draft generation') =>
    new DraftError(message, 'INVALID_PARAMETERS', 400, false),
} as const;
