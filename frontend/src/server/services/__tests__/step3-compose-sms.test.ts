/**
 * step3-compose-sms.test.ts - Step 3: Compose SMS Message
 *
 * TLA+ Properties:
 * - Reachability: Given valid payload with short summary → returns { message: string }
 * - TypeInvariant: Message is a string and length <= 160
 * - ErrorConsistency: Payload with very long summary producing >160 char message → throws SharedError SMS_TOO_LONG 422
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { SmsPayload } from '@/server/data_structures/FinalizeEvent';
import { SharedError } from '@/server/error_definitions/SharedErrors';

import { TriggerSmsFollowUpService } from '../TriggerSmsFollowUpService';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const shortPayload: SmsPayload = {
  answerSummary: 'My finalized answer',
  phoneNumber: '+15551234567',
};

const longPayload: SmsPayload = {
  answerSummary: 'A'.repeat(200),
  phoneNumber: '+15551234567',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TriggerSmsFollowUpService.composeSmsMessage — Step 3: Compose SMS Message', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return { message: string } for valid payload with short summary', () => {
      const result = TriggerSmsFollowUpService.composeSmsMessage(shortPayload);

      expect(result).toHaveProperty('message');
      expect(typeof result.message).toBe('string');
      expect(result.message.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return message that is a string with length <= 160', () => {
      const result = TriggerSmsFollowUpService.composeSmsMessage(shortPayload);

      expect(typeof result.message).toBe('string');
      expect(result.message.length).toBeLessThanOrEqual(160);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SharedError with code SMS_TOO_LONG when composed message exceeds 160 characters', () => {
      try {
        TriggerSmsFollowUpService.composeSmsMessage(longPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SharedError);
        expect((e as SharedError).code).toBe('SMS_TOO_LONG');
        expect((e as SharedError).statusCode).toBe(422);
      }
    });
  });
});
