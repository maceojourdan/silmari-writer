/**
 * SmsFollowupService.test.ts - Step 3: Send follow-up SMS
 *
 * TLA+ Properties:
 * - Reachability: Given eligible claim → SMS client called once, returns { status: 'sent' }
 * - TypeInvariant: Assert result type SmsSendResult (status: 'sent' | 'failed')
 * - ErrorConsistency (retry): Mock provider fail twice then succeed → service attempts 3 times, returns success
 * - ErrorConsistency (max fail): Mock provider always fail → after 3 attempts throw BackendErrors.SMS_SEND_FAILED
 *
 * Resource: db-h2s4 (service)
 * Path: 305-followup-sms-for-uncertain-claim
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { Claim, SmsSendResult } from '@/server/data_structures/Claim';
import { SmsError } from '@/server/error_definitions/SmsErrors';

// Mock the smsLogger
vi.mock('@/server/logging/smsLogger', () => ({
  smsLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SmsFollowupService } from '../SmsFollowupService';
import type { SmsClient, Timer } from '../SmsFollowupService';
import { smsLogger } from '@/server/logging/smsLogger';

const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const eligibleClaim: Claim = {
  id: 'claim-001',
  content: 'I increased sales by 40%',
  status: 'UNCERTAIN',
  smsOptIn: true,
  phoneNumber: '+15551234567',
  truth_checks: [],
  created_at: now,
  updated_at: now,
};

const claimWithoutPhone: Claim = {
  ...eligibleClaim,
  id: 'claim-no-phone',
  phoneNumber: undefined,
};

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

describe('SmsFollowupService.sendFollowup — Step 3: Send follow-up SMS', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return sent status on successful SMS send', async () => {
      const client = createMockClient([{ sid: 'SM-abc123' }]);

      const result = await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);

      expect(result.status).toBe('sent');
      expect(result.messageId).toBe('SM-abc123');
    });

    it('should call SMS client with claim phone number and composed message', async () => {
      const sendSpy = vi.fn().mockResolvedValue({ sid: 'SM-xyz' });
      const client: SmsClient = { sendMessage: sendSpy };

      await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);

      expect(sendSpy).toHaveBeenCalledOnce();
      expect(sendSpy).toHaveBeenCalledWith(
        '+15551234567',
        expect.stringContaining('I increased sales by 40%'),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return SmsSendResult with status "sent" on success', async () => {
      const client = createMockClient([{ sid: 'SM-type-check' }]);

      const result: SmsSendResult = await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);

      expect(result).toHaveProperty('status');
      expect(['sent', 'failed']).toContain(result.status);
      expect(result.status).toBe('sent');
    });

    it('should include messageId as a string when sent', async () => {
      const client = createMockClient([{ sid: 'SM-msg-id' }]);

      const result = await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);

      expect(typeof result.messageId).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should succeed after 2 failures followed by success (retry works)', async () => {
      const client = createMockClient([
        new Error('Provider timeout'),
        new Error('Provider timeout'),
        { sid: 'SM-recovered' },
      ]);

      const result = await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);

      expect(result.status).toBe('sent');
      expect(result.messageId).toBe('SM-recovered');
    });

    it('should throw SMS_SEND_FAILED after 3 consecutive failures', async () => {
      const client = createMockClient([
        new Error('Attempt 1 failed'),
        new Error('Attempt 2 failed'),
        new Error('Attempt 3 failed'),
      ]);

      try {
        await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('SMS_SEND_FAILED');
        expect((e as SmsError).statusCode).toBe(502);
        expect((e as SmsError).retryable).toBe(true);
      }
    });

    it('should log each failure attempt via smsLogger', async () => {
      const client = createMockClient([
        new Error('Fail 1'),
        new Error('Fail 2'),
        new Error('Fail 3'),
      ]);

      try {
        await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(3);
    });

    it('should log with claimId context on each failure', async () => {
      const client = createMockClient([
        new Error('Failed'),
        { sid: 'SM-ok' },
      ]);

      await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('attempt 1'),
        expect.any(Error),
        expect.objectContaining({ claimId: 'claim-001' }),
      );
    });

    it('should throw SMS_SEND_FAILED when claim has no phone number', async () => {
      const client = createMockClient([{ sid: 'SM-should-not-reach' }]);

      try {
        await SmsFollowupService.sendFollowup(claimWithoutPhone, client, instantTimer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('SMS_SEND_FAILED');
      }
    });

    it('should succeed on first attempt without logging errors', async () => {
      const client = createMockClient([{ sid: 'SM-first-try' }]);

      await SmsFollowupService.sendFollowup(eligibleClaim, client, instantTimer);

      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // Message composition
  // -------------------------------------------------------------------------

  describe('composeMessage', () => {
    it('should include claim content in the message', () => {
      const message = SmsFollowupService.composeMessage(eligibleClaim);

      expect(message).toContain('I increased sales by 40%');
    });

    it('should include instructions for CONFIRM or DENY reply', () => {
      const message = SmsFollowupService.composeMessage(eligibleClaim);

      expect(message).toContain('CONFIRM');
      expect(message).toContain('DENY');
    });
  });
});
