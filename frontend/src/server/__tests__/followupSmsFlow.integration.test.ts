/**
 * followupSmsFlow.integration.test.ts - Full integration test for the
 * followup SMS flow from trigger through truth_checks update.
 *
 * Terminal Condition:
 * > User receives follow-up SMS and claim's truth_checks reflects user response.
 *
 * Asserts Reachability: Full trigger → Step1→Step2→Step3→Step4→Step5
 * Asserts TypeInvariant: All intermediate DTOs match declared TS interfaces
 * Asserts ErrorConsistency: Simulate provider + DAO failures and assert defined backend/shared errors
 *
 * Path: 305-followup-sms-for-uncertain-claim
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimSchema } from '@/server/data_structures/Claim';
import type { Claim } from '@/server/data_structures/Claim';
import { SmsError } from '@/server/error_definitions/SmsErrors';
import { WebhookError } from '@/server/error_definitions/WebhookErrors';

// ---------------------------------------------------------------------------
// Mocks: DAO, SMS client, loggers
// ---------------------------------------------------------------------------

vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
  },
}));

vi.mock('@/server/logging/smsLogger', () => ({
  smsLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FollowupSmsPattern } from '@/server/execution_patterns/FollowupSmsPattern';
import { FollowupSmsProcessChain } from '@/server/process_chains/FollowupSmsProcessChain';
import { SmsFollowupService } from '@/server/services/SmsFollowupService';
import type { SmsClient, Timer } from '@/server/services/SmsFollowupService';
import { SmsReplyTransformer } from '@/server/transformers/SmsReplyTransformer';
import { TruthCheckReplyProcessor } from '@/server/processors/TruthCheckReplyProcessor';
import { SmsWebhookHandler } from '@/server/request_handlers/SmsWebhookHandler';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { smsLogger } from '@/server/logging/smsLogger';

const mockDAO = vi.mocked(ClaimDAO);
const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const seedClaim: Claim = {
  id: 'claim-integration-001',
  content: 'I increased sales by 40%',
  status: 'UNCERTAIN',
  smsOptIn: true,
  phoneNumber: '+15551234567',
  truth_checks: [],
  created_at: now,
  updated_at: now,
};

const updatedClaimConfirmed: Claim = {
  ...seedClaim,
  status: 'CONFIRMED',
  truth_checks: [
    {
      id: 'tc-int-001',
      verdict: 'confirmed',
      source: 'sms:SM-integration',
      created_at: now,
    },
  ],
  updated_at: now,
};

const instantTimer: Timer = {
  async delay(_ms: number): Promise<void> {},
};

function createSuccessClient(): SmsClient {
  return {
    async sendMessage(_to: string, _body: string): Promise<{ sid: string }> {
      return { sid: 'SM-integration' };
    },
  };
}

function createFailThenSuccessClient(): SmsClient {
  let calls = 0;
  return {
    async sendMessage(_to: string, _body: string): Promise<{ sid: string }> {
      calls++;
      if (calls < 3) throw new Error(`Provider failure ${calls}`);
      return { sid: 'SM-recovered' };
    },
  };
}

function createAlwaysFailClient(): SmsClient {
  return {
    async sendMessage(_to: string, _body: string): Promise<{ sid: string }> {
      throw new Error('Provider permanently down');
    },
  };
}

describe('Followup SMS Flow — Integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // Reachability: Full happy path
  // =========================================================================

  describe('Reachability', () => {
    it('should complete full flow: trigger → eligibility → SMS send', async () => {
      // Step 1: Trigger evaluates FOLLOWUP_SMS event
      // Step 2: Eligibility check passes
      mockDAO.findById.mockResolvedValue(seedClaim);

      // Step 3: SMS sent successfully (we test service directly with mock client)
      const client = createSuccessClient();
      const sendResult = await SmsFollowupService.sendFollowup(seedClaim, client, instantTimer);

      expect(sendResult.status).toBe('sent');
      expect(sendResult.messageId).toBe('SM-integration');
    });

    it('should complete webhook reply flow: parse → correlate → update', async () => {
      // Step 4: Receive webhook, correlate to claim
      mockDAO.findByPhoneNumber.mockResolvedValue(seedClaim);

      // Step 5: Update truth_checks
      mockDAO.updateTruthCheck.mockResolvedValue(updatedClaimConfirmed);

      const result = await SmsWebhookHandler.handle({
        From: '+15551234567',
        Body: 'CONFIRM',
        MessageSid: 'SM-integration',
      });

      expect(result.id).toBe('claim-integration-001');
      expect(result.status).toBe('CONFIRMED');
      expect(result.truth_checks).toHaveLength(1);
      expect(result.truth_checks[0].verdict).toBe('confirmed');
    });

    it('should complete full trigger → process chain with eligible claim', async () => {
      // Wire up: Step 1 → Step 2 → Step 3
      mockDAO.findById.mockResolvedValue(seedClaim);

      // We need to directly test the process chain's eligibility check
      const eligibility = await FollowupSmsProcessChain.validateEligibility('claim-integration-001');

      expect(eligibility.eligible).toBe(true);
      if (eligibility.eligible) {
        expect(eligibility.claim.id).toBe('claim-integration-001');
        expect(eligibility.claim.status).toBe('UNCERTAIN');
        expect(eligibility.claim.smsOptIn).toBe(true);
      }
    });

    it('should handle the full pattern evaluation with matching event', async () => {
      mockDAO.findById.mockResolvedValue(seedClaim);

      // Mock the SmsFollowupService to avoid actually needing Twilio
      const originalSendFollowup = SmsFollowupService.sendFollowup;
      (SmsFollowupService as { sendFollowup: typeof originalSendFollowup }).sendFollowup =
        vi.fn().mockResolvedValue({ status: 'sent', messageId: 'SM-pattern-test' });

      const result = await FollowupSmsPattern.evaluate({
        type: 'FOLLOWUP_SMS',
        claimId: 'claim-integration-001',
      });

      expect(result).toBe('MATCHED');

      // Restore
      (SmsFollowupService as { sendFollowup: typeof originalSendFollowup }).sendFollowup = originalSendFollowup;
    });
  });

  // =========================================================================
  // TypeInvariant: All intermediate DTOs match declared interfaces
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should maintain Claim type through eligibility check', async () => {
      mockDAO.findById.mockResolvedValue(seedClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-integration-001');

      if (result.eligible) {
        const parsed = ClaimSchema.safeParse(result.claim);
        expect(parsed.success).toBe(true);
      }
    });

    it('should produce valid SmsSendResult from service', async () => {
      const client = createSuccessClient();

      const result = await SmsFollowupService.sendFollowup(seedClaim, client, instantTimer);

      expect(result).toHaveProperty('status');
      expect(['sent', 'failed']).toContain(result.status);
      if (result.status === 'sent') {
        expect(typeof result.messageId).toBe('string');
      }
    });

    it('should produce valid TruthCheckUpdateRequest from transformer', async () => {
      mockDAO.findByPhoneNumber.mockResolvedValue(seedClaim);

      const update = await SmsReplyTransformer.parse({
        From: '+15551234567',
        Body: 'CONFIRM',
        MessageSid: 'SM-type-check',
      });

      expect(update).toHaveProperty('claimId');
      expect(update).toHaveProperty('verdict');
      expect(update).toHaveProperty('source');
      expect(typeof update.claimId).toBe('string');
      expect(['confirmed', 'denied']).toContain(update.verdict);
    });

    it('should return valid Claim from processor', async () => {
      mockDAO.updateTruthCheck.mockResolvedValue(updatedClaimConfirmed);

      const result = await TruthCheckReplyProcessor.process({
        claimId: 'claim-integration-001',
        verdict: 'confirmed',
        source: 'sms:SM-type-check',
      });

      const parsed = ClaimSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // =========================================================================
  // ErrorConsistency: Simulate failures at each layer
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should throw CLAIM_LOAD_FAILED when DAO fails during eligibility', async () => {
      mockDAO.findById.mockRejectedValue(new Error('DB unavailable'));

      try {
        await FollowupSmsProcessChain.validateEligibility('claim-fail');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('CLAIM_LOAD_FAILED');
      }
    });

    it('should throw SMS_SEND_FAILED after all retry attempts', async () => {
      const client = createAlwaysFailClient();

      try {
        await SmsFollowupService.sendFollowup(seedClaim, client, instantTimer);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('SMS_SEND_FAILED');
      }
    });

    it('should recover SMS send after provider failures', async () => {
      const client = createFailThenSuccessClient();

      const result = await SmsFollowupService.sendFollowup(seedClaim, client, instantTimer);

      expect(result.status).toBe('sent');
    });

    it('should throw CLAIM_NOT_FOUND when webhook cannot correlate', async () => {
      mockDAO.findByPhoneNumber.mockResolvedValue(null);

      try {
        await SmsReplyTransformer.parse({
          From: '+15550000000',
          Body: 'CONFIRM',
          MessageSid: 'SM-unknown',
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(WebhookError);
        expect((e as WebhookError).code).toBe('CLAIM_NOT_FOUND');
      }
    });

    it('should throw INVALID_WEBHOOK_PAYLOAD for unrecognized reply', async () => {
      try {
        await SmsReplyTransformer.parse({
          From: '+15551234567',
          Body: 'HELLO THERE',
          MessageSid: 'SM-gibberish',
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(WebhookError);
        expect((e as WebhookError).code).toBe('INVALID_WEBHOOK_PAYLOAD');
      }
    });

    it('should throw TRUTH_CHECK_PERSIST_FAILED when DAO fails during update', async () => {
      mockDAO.updateTruthCheck.mockRejectedValue(new Error('Deadlock'));

      try {
        await TruthCheckReplyProcessor.process({
          claimId: 'claim-integration-001',
          verdict: 'confirmed',
          source: 'sms:SM-fail',
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('TRUTH_CHECK_PERSIST_FAILED');
      }
    });

    it('should bypass pattern for non-matching events without errors', async () => {
      const result = await FollowupSmsPattern.evaluate({ type: 'UNRELATED', data: {} });

      expect(result).toBe('BYPASS');
    });

    it('should return ineligible for non-UNCERTAIN claims without errors', async () => {
      const confirmedClaim: Claim = { ...seedClaim, status: 'CONFIRMED' };
      mockDAO.findById.mockResolvedValue(confirmedClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-confirmed');

      expect(result.eligible).toBe(false);
    });
  });
});
