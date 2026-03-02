/**
 * step4-send-sms.test.ts - Step 4: Send SMS via Provider
 *
 * TLA+ Properties:
 * - Reachability: Provider returns success → { status: 'sent' }
 * - TypeInvariant: Response passes SmsDeliveryResponseSchema.safeParse()
 * - ErrorConsistency (retry): Transient error twice then success → 3 calls, returns success
 * - ErrorConsistency (max fail): Always failing → 3 attempts, throws SmsError PROVIDER_FAILURE, smsLogger.error called
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SmsDeliveryResponseSchema } from '@/server/data_structures/FinalizeEvent';
import { SmsError } from '@/server/error_definitions/SmsErrors';

// ---------------------------------------------------------------------------
// Mock smsLogger
// ---------------------------------------------------------------------------

vi.mock('@/server/logging/smsLogger', () => ({
  smsLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

import { TriggerSmsFollowUpService } from '../TriggerSmsFollowUpService';
import { smsLogger } from '@/server/logging/smsLogger';

const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// SMS Client and Timer interfaces (matching SmsFollowupService pattern)
// ---------------------------------------------------------------------------

interface SmsClient {
  sendMessage(to: string, body: string): Promise<{ sid: string }>;
}

interface Timer {
  delay(ms: number): Promise<void>;
}

// No-op timer for tests (no actual delays)
const instantTimer: Timer = {
  async delay(_ms: number): Promise<void> {
    // Instant - no delay
  },
};

function createMockClient(responses: Array<{ sid: string } | Error>): SmsClient {
  let callCount = 0;
  return {
    async sendMessage(_to: string, _body: string): Promise<{ sid: string }> {
      const response = responses[callCount++];
      if (response instanceof Error) {
        throw response;
      }
      return response;
    },
  };
}

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const testMessage = 'Your answer has been finalized. Thank you!';
const testPhone = '+15551234567';

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TriggerSmsFollowUpService.sendSms — Step 4: Send SMS via Provider', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return { status: "sent" } when provider returns success', async () => {
      const client = createMockClient([{ sid: 'SM-abc123' }]);

      const result = await TriggerSmsFollowUpService.sendSms(testMessage, testPhone, client, instantTimer);

      expect(result.status).toBe('sent');
    });

    it('should include messageId from provider sid on success', async () => {
      const client = createMockClient([{ sid: 'SM-msg-001' }]);

      const result = await TriggerSmsFollowUpService.sendSms(testMessage, testPhone, client, instantTimer);

      expect(result.messageId).toBe('SM-msg-001');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object passing SmsDeliveryResponseSchema validation', async () => {
      const client = createMockClient([{ sid: 'SM-type-check' }]);

      const result = await TriggerSmsFollowUpService.sendSms(testMessage, testPhone, client, instantTimer);
      const parsed = SmsDeliveryResponseSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should succeed after 2 transient failures followed by success (3 calls made)', async () => {
      const sendSpy = vi.fn()
        .mockRejectedValueOnce(new Error('Provider timeout'))
        .mockRejectedValueOnce(new Error('Provider timeout'))
        .mockResolvedValueOnce({ sid: 'SM-recovered' });
      const client: SmsClient = { sendMessage: sendSpy };

      const result = await TriggerSmsFollowUpService.sendSms(testMessage, testPhone, client, instantTimer);

      expect(result.status).toBe('sent');
      expect(result.messageId).toBe('SM-recovered');
      expect(sendSpy).toHaveBeenCalledTimes(3);
    });

    it('should throw SmsError with code PROVIDER_FAILURE after 3 consecutive failures', async () => {
      const client = createMockClient([
        new Error('Attempt 1 failed'),
        new Error('Attempt 2 failed'),
        new Error('Attempt 3 failed'),
      ]);

      try {
        await TriggerSmsFollowUpService.sendSms(testMessage, testPhone, client, instantTimer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('PROVIDER_FAILURE');
      }
    });

    it('should call smsLogger.error on each failed attempt', async () => {
      const client = createMockClient([
        new Error('Fail 1'),
        new Error('Fail 2'),
        new Error('Fail 3'),
      ]);

      try {
        await TriggerSmsFollowUpService.sendSms(testMessage, testPhone, client, instantTimer);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(3);
    });

    it('should not log errors when first attempt succeeds', async () => {
      const client = createMockClient([{ sid: 'SM-first-try' }]);

      await TriggerSmsFollowUpService.sendSms(testMessage, testPhone, client, instantTimer);

      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });
});
