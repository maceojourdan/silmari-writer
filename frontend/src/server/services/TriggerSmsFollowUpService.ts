/**
 * TriggerSmsFollowUpService - Orchestrates SMS follow-up on answer finalization.
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 *
 * Steps:
 * 1. Detect finalize completion event
 * 2. Load answer and contact data
 * 3. Compose SMS follow-up message
 * 4. Send SMS via external provider
 * 5. Record SMS dispatch result
 */

import { FinalizeEventSchema } from '@/server/data_structures/FinalizeEvent';
import type {
  FinalizeEvent,
  DetectFinalizeResult,
  SmsPayload,
  SmsDeliveryResponse,
} from '@/server/data_structures/FinalizeEvent';
import type { SmsFollowUpRecord } from '@/server/data_structures/SmsFollowUpRecord';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';
import { SmsFollowUpErrors } from '@/server/error_definitions/SmsErrors';
import { AnswerDAO } from '@/server/data_access_objects/AnswerDAO';
import { UserDAO } from '@/server/data_access_objects/UserDAO';
import { SmsFollowUpDAO } from '@/server/data_access_objects/SmsFollowUpDAO';
import { smsLogger } from '@/server/logging/smsLogger';
import { SmsProviderSettings } from '@/server/settings/SmsProviderSettings';

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
// Constants
// ---------------------------------------------------------------------------

const SMS_MAX_LENGTH = 160;
const E164_REGEX = /^\+[1-9]\d{1,14}$/;

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const TriggerSmsFollowUpService = {
  /**
   * Step 1: Detect whether a finalize event should trigger an SMS follow-up.
   *
   * Validates the event via Zod, checks smsOptIn flag and phone number format.
   * Returns { shouldSend: false } when SMS is not opted in.
   * Returns { shouldSend: true, answerId, phoneNumber } when valid.
   * Throws SharedErrors.MissingPhoneNumber on invalid/missing phone.
   */
  detectFinalizeCompletion(event: FinalizeEvent): DetectFinalizeResult {
    FinalizeEventSchema.parse(event);

    if (event.smsOptIn === false) {
      return { shouldSend: false };
    }

    if (!event.phoneNumber || !E164_REGEX.test(event.phoneNumber)) {
      throw SharedErrors.MissingPhoneNumber();
    }

    return {
      shouldSend: true,
      answerId: event.answerId,
      phoneNumber: event.phoneNumber,
    };
  },

  /**
   * Step 2: Load the answer and user contact data from DAOs.
   *
   * Throws SmsFollowUpErrors.ANSWER_NOT_FOUND if answer is null.
   * Throws SmsFollowUpErrors.DATABASE_FAILURE on DAO errors or missing user.
   */
  async loadAnswerAndContact(answerId: string, userId: string): Promise<SmsPayload> {
    let answer;
    try {
      answer = await AnswerDAO.findById(answerId);
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown DAO error';
      throw SmsFollowUpErrors.DATABASE_FAILURE(message);
    }

    if (!answer) {
      throw SmsFollowUpErrors.ANSWER_NOT_FOUND();
    }

    let user;
    try {
      user = await UserDAO.findById(userId);
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown DAO error';
      throw SmsFollowUpErrors.DATABASE_FAILURE(message);
    }

    if (!user) {
      throw SmsFollowUpErrors.DATABASE_FAILURE('User not found');
    }

    // Truncate answer content to first 100 chars if needed
    const answerSummary = answer.content.length > 100
      ? answer.content.slice(0, 100)
      : answer.content;

    return {
      answerSummary,
      phoneNumber: user.phoneNumber!,
    };
  },

  /**
   * Step 3: Compose the SMS follow-up message from the payload.
   *
   * Builds a deterministic template string from the answer summary.
   * Throws SharedErrors.SmsTooLong if the composed message exceeds 160 characters.
   */
  composeSmsMessage(payload: SmsPayload): { message: string } {
    const prefix = 'Your answer has been finalized: ';
    const message = `${prefix}${payload.answerSummary}`;

    if (message.length > SMS_MAX_LENGTH) {
      throw SharedErrors.SmsTooLong();
    }

    return { message };
  },

  /**
   * Step 4: Send SMS via external provider with retry logic.
   *
   * Retries up to 3 times with exponential backoff (1s, 2s delays).
   * Throws SmsFollowUpErrors.PROVIDER_FAILURE after all attempts exhausted.
   */
  async sendSms(
    message: string,
    phoneNumber: string,
    client: SmsClient = defaultSmsClient,
    timer: Timer = defaultTimer,
  ): Promise<SmsDeliveryResponse> {
    const maxAttempts = 3;

    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
      try {
        const result = await client.sendMessage(phoneNumber, message);
        return { status: 'sent', messageId: result.sid };
      } catch (error) {
        smsLogger.error(
          `SMS send attempt ${attempt}/${maxAttempts} failed`,
          error,
          { phoneNumber, attempt },
        );

        if (attempt === maxAttempts) {
          throw SmsFollowUpErrors.PROVIDER_FAILURE();
        }

        // Exponential backoff: 1s, 2s
        await timer.delay(Math.pow(2, attempt - 1) * 1000);
      }
    }

    // Unreachable, but TypeScript needs this
    throw SmsFollowUpErrors.PROVIDER_FAILURE();
  },

  /**
   * Step 5: Record the SMS dispatch result in the database.
   *
   * Throws SmsFollowUpErrors.PERSISTENCE_FAILURE if the DAO insert fails.
   */
  async recordResult(
    deliveryResponse: SmsDeliveryResponse,
    answerId: string,
    phoneNumber: string,
    message: string,
  ): Promise<SmsFollowUpRecord> {
    const record = {
      answerId,
      phoneNumber,
      message,
      status: deliveryResponse.status,
      messageId: deliveryResponse.messageId,
      createdAt: new Date().toISOString(),
    };

    try {
      const persisted = await SmsFollowUpDAO.insert(record);
      smsLogger.info('SMS follow-up record persisted', { answerId });
      return persisted;
    } catch (error) {
      smsLogger.critical('Failed to persist SMS follow-up record', error, { answerId });
      throw SmsFollowUpErrors.PERSISTENCE_FAILURE();
    }
  },

  /**
   * Main orchestrator: handles the full finalize-event-to-SMS pipeline.
   *
   * Calls steps 1-5 in sequence. Returns early with { status: 'completed' }
   * if SMS opt-in is false (no-op).
   */
  async handleFinalizeEvent(event: FinalizeEvent): Promise<{ status: 'completed' }> {
    // Step 1: Detect whether SMS should be sent
    const detection = this.detectFinalizeCompletion(event);

    if (!detection.shouldSend) {
      return { status: 'completed' };
    }

    // Step 2: Load answer and contact data
    const payload = await this.loadAnswerAndContact(detection.answerId, event.userId);

    // Step 3: Compose SMS message
    const { message } = this.composeSmsMessage(payload);

    // Step 4: Send SMS via external provider
    const deliveryResponse = await this.sendSms(message, payload.phoneNumber);

    // Step 5: Record dispatch result
    await this.recordResult(deliveryResponse, detection.answerId, payload.phoneNumber, message);

    return { status: 'completed' };
  },
} as const;
