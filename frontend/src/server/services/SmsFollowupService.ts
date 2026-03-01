/**
 * SmsFollowupService - Orchestrates SMS sending with retry logic.
 *
 * Resource: db-h2s4 (service)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * Composes a follow-up message and sends via Twilio SDK.
 * Retries up to 3 times with exponential backoff on failure.
 */

import type { Claim, SmsSendResult } from '@/server/data_structures/Claim';
import { BackendErrors } from '@/server/error_definitions/SmsErrors';
import { smsLogger } from '@/server/logging/smsLogger';

// ---------------------------------------------------------------------------
// SMS Client Interface (mockable)
// ---------------------------------------------------------------------------

export interface SmsClient {
  sendMessage(to: string, body: string): Promise<{ sid: string }>;
}

// ---------------------------------------------------------------------------
// Default SMS client stub (not yet wired to Twilio)
// ---------------------------------------------------------------------------

const defaultSmsClient: SmsClient = {
  async sendMessage(_to: string, _body: string): Promise<{ sid: string }> {
    throw new Error('SmsClient.sendMessage not yet wired to Twilio');
  },
};

// ---------------------------------------------------------------------------
// Timer interface for mockable delays
// ---------------------------------------------------------------------------

export interface Timer {
  delay(ms: number): Promise<void>;
}

const defaultTimer: Timer = {
  async delay(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  },
};

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const SmsFollowupService = {
  /**
   * Compose a follow-up message for the uncertain claim.
   */
  composeMessage(claim: Claim): string {
    return `Hi! We'd like to follow up on your claim: "${claim.content}". ` +
      `Please reply CONFIRM or DENY to verify this claim.`;
  },

  /**
   * Send follow-up SMS with retry logic.
   *
   * Retries up to 3 times with exponential backoff.
   * Throws BackendErrors.SMS_SEND_FAILED after all attempts exhausted.
   */
  async sendFollowup(
    claim: Claim,
    client: SmsClient = defaultSmsClient,
    timer: Timer = defaultTimer,
  ): Promise<SmsSendResult> {
    if (!claim.phoneNumber) {
      throw BackendErrors.SMS_SEND_FAILED(`Claim ${claim.id} has no phone number`);
    }

    const message = this.composeMessage(claim);
    const maxAttempts = 3;

    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
      try {
        const result = await client.sendMessage(claim.phoneNumber, message);
        return { status: 'sent', messageId: result.sid };
      } catch (error) {
        smsLogger.error(
          `SMS send attempt ${attempt}/${maxAttempts} failed`,
          error,
          { claimId: claim.id, phoneNumber: claim.phoneNumber },
        );

        if (attempt === maxAttempts) {
          throw BackendErrors.SMS_SEND_FAILED(
            `Failed to send SMS after ${maxAttempts} attempts for claim ${claim.id}`,
          );
        }

        // Exponential backoff: 1s, 2s
        await timer.delay(Math.pow(2, attempt - 1) * 1000);
      }
    }

    // Unreachable, but TypeScript needs this
    throw BackendErrors.SMS_SEND_FAILED();
  },
} as const;
