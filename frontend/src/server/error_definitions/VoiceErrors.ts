/**
 * VoiceErrors - Standardized error definitions for the voice/SAY event path.
 *
 * Covers payload validation, session verification, speech transformation,
 * audio synthesis, and transcript dispatch failures.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Paths:
 *   - 304-backend-say-event-triggers-voice-and-transcript
 *   - 317-prompt-for-missing-slots-after-partial-voice-answer
 *   - 318-complete-voice-answer-advances-workflow
 */

export type VoiceErrorCode =
  | 'INVALID_SAY_PAYLOAD'
  | 'SESSION_INACTIVE'
  | 'TRANSCRIPTION_FAILED'
  | 'TRANSFORMATION_FAILED'
  | 'SYNTHESIS_FAILED'
  | 'TRANSCRIPT_DISPATCH_FAILED'
  | 'VOICE_RECOGNITION_FAILED'
  | 'SLOT_VALIDATION_FAILED'
  | 'CONFIGURATION_ERROR'
  | 'VOICE_DELIVERY_FAILED'
  | 'VALIDATION_FAILED'
  | 'VOICE_INIT_FAILED'
  | 'VOICE_INPUT_INVALID'
  | 'GENERIC_VOICE_ERROR';

export class VoiceError extends Error {
  code: VoiceErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: VoiceErrorCode,
    statusCode: number = 500,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'VoiceError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

// ---------------------------------------------------------------------------
// Step 1: Intercept SAY event — payload validation
// ---------------------------------------------------------------------------

export const VoicePayloadError = {
  INVALID_SAY_PAYLOAD: (message = 'SAY event payload is malformed or missing required fields') =>
    new VoiceError(message, 'INVALID_SAY_PAYLOAD', 400, false),
} as const;

// ---------------------------------------------------------------------------
// Step 2: Validate session context — session state
// ---------------------------------------------------------------------------

export const VoiceSessionError = {
  SESSION_INACTIVE: (message = 'Session is inactive or not found') =>
    new VoiceError(message, 'SESSION_INACTIVE', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Step 3: Transform prompt to speech request — transformation
// ---------------------------------------------------------------------------

export const VoiceTransformError = {
  TRANSFORMATION_FAILED: (message = 'Failed to transform prompt into speech request') =>
    new VoiceError(message, 'TRANSFORMATION_FAILED', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Step 4: Synthesize and stream audio — synthesis
// ---------------------------------------------------------------------------

export const VoiceSynthesisError = {
  SYNTHESIS_FAILED: (message = 'Speech synthesis failed after all retry attempts') =>
    new VoiceError(message, 'SYNTHESIS_FAILED', 502, true),
} as const;

// ---------------------------------------------------------------------------
// Step 5: Emit TRANSCRIPT_FINAL — dispatch
// ---------------------------------------------------------------------------

export const VoiceDispatchError = {
  TRANSCRIPT_DISPATCH_FAILED: (message = 'Failed to dispatch TRANSCRIPT_FINAL event after all retry attempts') =>
    new VoiceError(message, 'TRANSCRIPT_DISPATCH_FAILED', 502, true),
} as const;

// ---------------------------------------------------------------------------
// Path 317: Voice recognition — speech capture failures
// ---------------------------------------------------------------------------

export const VoiceRecognitionError = {
  VOICE_RECOGNITION_FAILED: (message = 'Speech recognition failed or returned empty output') =>
    new VoiceError(message, 'VOICE_RECOGNITION_FAILED', 422, true),
} as const;

// ---------------------------------------------------------------------------
// Path 317: Slot validation — invalid slot values
// ---------------------------------------------------------------------------

export const SlotValidationError = {
  SLOT_VALIDATION_FAILED: (message = 'Slot value failed validation') =>
    new VoiceError(message, 'SLOT_VALIDATION_FAILED', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Path 317: Configuration — missing required slot definitions
// ---------------------------------------------------------------------------

export const VoiceConfigurationError = {
  CONFIGURATION_ERROR: (message = 'Question type configuration is missing required slot definitions') =>
    new VoiceError(message, 'CONFIGURATION_ERROR', 500, false),
} as const;

// ---------------------------------------------------------------------------
// Path 317: Voice delivery — synthesis/playback failure
// ---------------------------------------------------------------------------

export const VoiceDeliveryError = {
  VOICE_DELIVERY_FAILED: (message = 'Voice follow-up delivery failed') =>
    new VoiceError(message, 'VOICE_DELIVERY_FAILED', 502, true),
} as const;

// ---------------------------------------------------------------------------
// Path 318: Transcription — audio-to-text failure
// ---------------------------------------------------------------------------

export const VoiceTranscriptionError = {
  TRANSCRIPTION_FAILED: (message = 'Transcription failed or audio is empty') =>
    new VoiceError(message, 'TRANSCRIPTION_FAILED', 422, true),
} as const;

// ---------------------------------------------------------------------------
// Path 318: Validation — minimum slot validation failure
// ---------------------------------------------------------------------------

export const VoiceValidationError = {
  VALIDATION_FAILED: (message = 'Minimum required slots not satisfied') =>
    new VoiceError(message, 'VALIDATION_FAILED', 422, false),
} as const;

// ---------------------------------------------------------------------------
// Path 332: Voice input validation — initialization and input failures
// ---------------------------------------------------------------------------

export const VoiceInitError = {
  VOICE_INIT_FAILED: (message = 'Unable to start voice capture. Please try again.') =>
    new VoiceError(message, 'VOICE_INIT_FAILED', 500, true),
} as const;

export const VoiceInputError = {
  VOICE_INPUT_INVALID: (message = 'Voice input could not be processed.') =>
    new VoiceError(message, 'VOICE_INPUT_INVALID', 422, false),
} as const;

export const GenericVoiceError = {
  GENERIC_VOICE_ERROR: (message = 'Something went wrong with voice input.') =>
    new VoiceError(message, 'GENERIC_VOICE_ERROR', 500, false),
} as const;

// ---------------------------------------------------------------------------
// Path 332: Simple constant error definitions for frontend validation
// These are lightweight objects used by VoiceInputVerifier and ReviewScreen
// to avoid constructing Error instances for simple validation failures.
// ---------------------------------------------------------------------------

export interface VoiceErrorDef {
  code: string;
  message: string;
}

export const VoiceInputErrors = {
  VOICE_INIT_FAILED: {
    code: 'VOICE_INIT_FAILED' as const,
    message: 'Unable to start voice capture. Please try again.',
  },
  VOICE_INPUT_INVALID: {
    code: 'VOICE_INPUT_INVALID' as const,
    message: 'Voice input could not be processed.',
  },
  GENERIC_VOICE_ERROR: {
    code: 'GENERIC_VOICE_ERROR' as const,
    message: 'Something went wrong with voice input.',
  },
} as const;

// ---------------------------------------------------------------------------
// Convenience aggregate — all error factories
// ---------------------------------------------------------------------------

export const VoiceErrors = {
  ...VoicePayloadError,
  ...VoiceSessionError,
  ...VoiceTranscriptionError,
  ...VoiceTransformError,
  ...VoiceSynthesisError,
  ...VoiceDispatchError,
  ...VoiceRecognitionError,
  ...SlotValidationError,
  ...VoiceConfigurationError,
  ...VoiceDeliveryError,
  ...VoiceValidationError,
  ...VoiceInitError,
  ...VoiceInputError,
  ...GenericVoiceError,
} as const;
