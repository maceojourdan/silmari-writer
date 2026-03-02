/**
 * VoiceInputVerifier - Validates voice input existence and intelligibility
 * before submission to backend.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 332-voice-edit-no-input-error-on-review-screen
 *
 * Validates:
 *   - Transcript is non-empty
 *   - Transcript meets minimum intelligibility threshold (>= 3 chars after trim)
 *
 * Returns:
 *   - { valid: true, payload: VoicePayload } on success
 *   - { valid: false, error: VoiceErrorDef } on failure
 */

import { VoiceInputErrors } from '@/server/error_definitions/VoiceErrors';
import type { VoiceErrorDef } from '@/server/error_definitions/VoiceErrors';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type VoicePayload = {
  transcript: string;
  durationMs: number;
};

type ValidationSuccess = { valid: true; payload: VoicePayload };
type ValidationFailure = { valid: false; error: VoiceErrorDef };
export type VoiceInputValidationResult = ValidationSuccess | ValidationFailure;

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

const MIN_TRANSCRIPT_LENGTH = 3;

export function validateVoiceInput(
  transcript: string,
  durationMs: number,
): VoiceInputValidationResult {
  if (!transcript || transcript.trim().length < MIN_TRANSCRIPT_LENGTH) {
    return { valid: false, error: VoiceInputErrors.VOICE_INPUT_INVALID };
  }

  return {
    valid: true,
    payload: { transcript: transcript.trim(), durationMs },
  };
}
