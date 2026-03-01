/**
 * verificationTimeout - Configuration for verification timeout duration.
 *
 * Resource: cfg-l8y1 (shared_settings)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * In production, this would load from environment variables or a config
 * service. Designed to be mockable for TDD.
 */

/** Default verification timeout: 5 minutes (300,000 ms) */
const DEFAULT_VERIFICATION_TIMEOUT_MS = 5 * 60 * 1000;

/**
 * Returns the configured verification timeout in milliseconds.
 *
 * Reads from VERIFICATION_TIMEOUT_MS environment variable if set,
 * otherwise falls back to the default of 5 minutes.
 *
 * @throws Error if the environment variable is set but not a valid number.
 */
export function getVerificationTimeoutMs(): number {
  const envValue = process.env.VERIFICATION_TIMEOUT_MS;

  if (envValue === undefined || envValue === '') {
    return DEFAULT_VERIFICATION_TIMEOUT_MS;
  }

  const parsed = Number(envValue);

  if (Number.isNaN(parsed) || parsed <= 0) {
    throw new Error(
      `Invalid VERIFICATION_TIMEOUT_MS: "${envValue}". Must be a positive number.`,
    );
  }

  return parsed;
}
