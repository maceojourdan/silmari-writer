/**
 * consentVerifier - Validates that consent response is explicitly affirmative.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * Only explicitly affirmative responses ("yes", "I agree") are accepted.
 * All other inputs (including undefined, null, empty, arbitrary text) return false.
 */

const AFFIRMATIVE_RESPONSES = new Set(['yes', 'i agree']);

/**
 * Checks whether the user's consent response is explicitly affirmative.
 *
 * @param input - The user's response string
 * @returns true only if the response is an explicitly affirmative value
 */
export function isExplicitlyAffirmative(input: string): boolean {
  if (typeof input !== 'string') {
    return false;
  }

  const normalized = input.trim().toLowerCase();
  return AFFIRMATIVE_RESPONSES.has(normalized);
}
