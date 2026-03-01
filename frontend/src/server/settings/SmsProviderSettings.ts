/**
 * SmsProviderSettings - Loads and provides SMS provider configuration.
 *
 * Resource: cfg-m2z6 (backend_settings)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * In production, credentials are loaded from environment variables.
 * For TDD, the settings object is designed to be mockable.
 */

export interface SmsProviderConfig {
  accountSid: string;
  authToken: string;
  fromNumber: string;
}

export const SmsProviderSettings = {
  /**
   * Load SMS provider configuration from environment variables.
   */
  load(): SmsProviderConfig {
    const accountSid = process.env.TWILIO_ACCOUNT_SID;
    const authToken = process.env.TWILIO_AUTH_TOKEN;
    const fromNumber = process.env.TWILIO_FROM_NUMBER;

    if (!accountSid || !authToken || !fromNumber) {
      throw new Error(
        'Missing SMS provider configuration: TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN, and TWILIO_FROM_NUMBER must be set',
      );
    }

    return { accountSid, authToken, fromNumber };
  },
} as const;
