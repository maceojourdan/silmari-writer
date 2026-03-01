/**
 * SmsWebhookHandler.test.ts - Step 4: Receive SMS reply webhook
 *
 * TLA+ Properties:
 * - Reachability: POST valid Twilio payload → handler returns updated claim
 *   and calls TruthCheckReplyProcessor.process(structuredUpdate)
 * - TypeInvariant: Assert transformer returns TruthCheckUpdateRequest with claimId + verdict
 * - ErrorConsistency: Invalid/missing claim correlation → WebhookErrors.CLAIM_NOT_FOUND
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 305-followup-sms-for-uncertain-claim
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { Claim, TruthCheckUpdateRequest } from '@/server/data_structures/Claim';
import { WebhookError, WebhookErrors } from '@/server/error_definitions/WebhookErrors';
import { SmsError } from '@/server/error_definitions/SmsErrors';

// Mock dependencies
vi.mock('@/server/transformers/SmsReplyTransformer', () => ({
  SmsReplyTransformer: {
    parse: vi.fn(),
    parsePayload: vi.fn(),
    extractVerdict: vi.fn(),
  },
}));

vi.mock('@/server/processors/TruthCheckReplyProcessor', () => ({
  TruthCheckReplyProcessor: {
    process: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SmsWebhookHandler } from '../SmsWebhookHandler';
import { SmsReplyTransformer } from '@/server/transformers/SmsReplyTransformer';
import { TruthCheckReplyProcessor } from '@/server/processors/TruthCheckReplyProcessor';
import { logger } from '@/server/logging/logger';

const mockTransformer = vi.mocked(SmsReplyTransformer);
const mockProcessor = vi.mocked(TruthCheckReplyProcessor);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const validTwilioPayload = {
  From: '+15551234567',
  Body: 'CONFIRM',
  MessageSid: 'SM-abc123',
  To: '+15559876543',
  AccountSid: 'AC-test',
};

const structuredUpdate: TruthCheckUpdateRequest = {
  claimId: 'claim-001',
  verdict: 'confirmed',
  source: 'sms:SM-abc123',
};

const updatedClaim: Claim = {
  id: 'claim-001',
  content: 'I increased sales by 40%',
  status: 'CONFIRMED',
  smsOptIn: true,
  phoneNumber: '+15551234567',
  truth_checks: [
    {
      id: 'tc-001',
      verdict: 'confirmed',
      source: 'sms:SM-abc123',
      created_at: now,
    },
  ],
  created_at: now,
  updated_at: now,
};

describe('SmsWebhookHandler.handle — Step 4: Receive SMS reply webhook', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return updated claim on valid payload', async () => {
      mockTransformer.parse.mockResolvedValue(structuredUpdate);
      mockProcessor.process.mockResolvedValue(updatedClaim);

      const result = await SmsWebhookHandler.handle(validTwilioPayload);

      expect(result).toEqual(updatedClaim);
    });

    it('should call SmsReplyTransformer.parse with the payload', async () => {
      mockTransformer.parse.mockResolvedValue(structuredUpdate);
      mockProcessor.process.mockResolvedValue(updatedClaim);

      await SmsWebhookHandler.handle(validTwilioPayload);

      expect(mockTransformer.parse).toHaveBeenCalledOnce();
      expect(mockTransformer.parse).toHaveBeenCalledWith(validTwilioPayload);
    });

    it('should call TruthCheckReplyProcessor.process with structured update', async () => {
      mockTransformer.parse.mockResolvedValue(structuredUpdate);
      mockProcessor.process.mockResolvedValue(updatedClaim);

      await SmsWebhookHandler.handle(validTwilioPayload);

      expect(mockProcessor.process).toHaveBeenCalledOnce();
      expect(mockProcessor.process).toHaveBeenCalledWith(structuredUpdate);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass TruthCheckUpdateRequest with claimId and verdict to processor', async () => {
      mockTransformer.parse.mockResolvedValue(structuredUpdate);
      mockProcessor.process.mockResolvedValue(updatedClaim);

      await SmsWebhookHandler.handle(validTwilioPayload);

      const processArg = mockProcessor.process.mock.calls[0][0];
      expect(processArg).toHaveProperty('claimId');
      expect(processArg).toHaveProperty('verdict');
      expect(typeof processArg.claimId).toBe('string');
      expect(['confirmed', 'denied']).toContain(processArg.verdict);
    });

    it('should return a Claim object with updated status', async () => {
      mockTransformer.parse.mockResolvedValue(structuredUpdate);
      mockProcessor.process.mockResolvedValue(updatedClaim);

      const result = await SmsWebhookHandler.handle(validTwilioPayload);

      expect(result).toHaveProperty('id');
      expect(result).toHaveProperty('status');
      expect(result).toHaveProperty('truth_checks');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow WebhookError.CLAIM_NOT_FOUND when correlation fails', async () => {
      mockTransformer.parse.mockRejectedValue(
        WebhookErrors.CLAIM_NOT_FOUND('No claim for +15550000000'),
      );

      try {
        await SmsWebhookHandler.handle({ From: '+15550000000', Body: 'CONFIRM', MessageSid: 'SM-x' });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(WebhookError);
        expect((e as WebhookError).code).toBe('CLAIM_NOT_FOUND');
        expect((e as WebhookError).statusCode).toBe(400);
      }
    });

    it('should rethrow WebhookError.INVALID_WEBHOOK_PAYLOAD on malformed payload', async () => {
      mockTransformer.parse.mockRejectedValue(
        WebhookErrors.INVALID_WEBHOOK_PAYLOAD('Missing required fields'),
      );

      try {
        await SmsWebhookHandler.handle({});
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(WebhookError);
        expect((e as WebhookError).code).toBe('INVALID_WEBHOOK_PAYLOAD');
      }
    });

    it('should rethrow SmsError when processor throws', async () => {
      const { BackendErrors } = await import('@/server/error_definitions/SmsErrors');
      mockTransformer.parse.mockResolvedValue(structuredUpdate);
      mockProcessor.process.mockRejectedValue(
        BackendErrors.TRUTH_CHECK_PERSIST_FAILED('DB error'),
      );

      try {
        await SmsWebhookHandler.handle(validTwilioPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('TRUTH_CHECK_PERSIST_FAILED');
      }
    });

    it('should log and wrap unknown errors as GenericError', async () => {
      mockTransformer.parse.mockRejectedValue(new TypeError('unexpected'));

      try {
        await SmsWebhookHandler.handle(validTwilioPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as Error).name).toBe('GenericError');
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Unexpected error'),
        expect.any(TypeError),
        expect.objectContaining({
          path: '305-followup-sms-for-uncertain-claim',
          resource: 'api-n8k2',
        }),
      );
    });
  });
});
