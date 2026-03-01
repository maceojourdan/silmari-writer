/**
 * EditByVoiceErrors - Structured error definitions for the edit-by-voice path.
 *
 * Covers invalid instruction and persistence failure errors
 * for the 330-edit-content-by-voice-from-review-screen path.
 *
 * Resource: db-l1c3 (backend_error_definitions)
 * Path: 330-edit-content-by-voice-from-review-screen
 */

export type EditByVoiceErrorCode =
  | 'INVALID_INSTRUCTION'
  | 'PERSISTENCE_FAILURE'
  | 'CONTENT_NOT_FOUND';

export class EditByVoiceError extends Error {
  code: EditByVoiceErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: EditByVoiceErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'EditByVoiceError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Instruction errors — Step 3: process voice instruction
// ---------------------------------------------------------------------------

export const EditByVoiceInstructionError = {
  INVALID_INSTRUCTION: (message = 'Voice instruction is semantically invalid or cannot be processed') =>
    new EditByVoiceError(message, 'INVALID_INSTRUCTION', 422, false),

  CONTENT_NOT_FOUND: (message = 'Content not found') =>
    new EditByVoiceError(message, 'CONTENT_NOT_FOUND', 404, false),
} as const;

// ---------------------------------------------------------------------------
// Persistence errors — Step 4: persist revised content
// ---------------------------------------------------------------------------

export const EditByVoicePersistenceError = {
  PERSISTENCE_FAILURE: (message = 'Failed to persist revised content') =>
    new EditByVoiceError(message, 'PERSISTENCE_FAILURE', 500, true),
} as const;
