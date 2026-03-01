/**
 * VoiceSessionService - Validates consent and controls session initialization.
 *
 * Resource: db-h2s4 (service)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * Verifies that affirmative consent flag is present and strictly true
 * before allowing voice session initialization.
 * Throws ConsentErrors.ConsentRequired on failure.
 */

import { ConsentErrors } from '@/server/error_definitions/ConsentErrors';

export interface ConsentValidationResult {
  authorized: boolean;
  sessionStatus: 'INIT';
}

export const VoiceSessionService = {
  /**
   * Validate that consent payload contains explicit affirmative consent.
   *
   * @param payload - Object containing consent flag
   * @returns ConsentValidationResult with authorized: true and sessionStatus: 'INIT'
   * @throws ConsentError with code CONSENT_REQUIRED if consent is not strictly true
   */
  validateConsent(payload: { consent: boolean }): ConsentValidationResult {
    if (payload.consent !== true) {
      throw ConsentErrors.ConsentRequired();
    }

    return {
      authorized: true,
      sessionStatus: 'INIT',
    };
  },
} as const;
