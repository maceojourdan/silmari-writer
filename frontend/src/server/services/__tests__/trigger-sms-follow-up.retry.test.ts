/**
 * trigger-sms-follow-up.retry.test.ts - Feedback Loop: Retry Behavior
 *
 * Tests the SMS send retry logic within TriggerSmsFollowUpService.sendSms:
 * - Transient failure recovery (2 failures + success)
 * - Schema conformance of response
 * - Max retry exhaustion (3 consecutive failures → PROVIDER_FAILURE)
 * - Backoff timing enforcement
 *
 * TLA+ Properties:
 * - Reachability: transient failures → eventual success through retry loop
 * - TypeInvariant: response conforms to SmsDeliveryResponseSchema
 * - ErrorConsistency: exhausted retries → PROVIDER_FAILURE with structured error
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SmsDeliveryResponseSchema } from '@/server/data_structures/FinalizeEvent';
import { SmsError } from '@/server/error_definitions/SmsErrors';

// ---------------------------------------------------------------------------
// Mock logger
// ---------------------------------------------------------------------------

vi.mock('@/server/logging/smsLogger', () => ({
  smsLogger: { info: vi.fn(), warn: vi.fn(), error: vi.fn(), critical: vi.fn() },
}));

// ---------------------------------------------------------------------------
// Imports (must come after vi.mock)
// ---------------------------------------------------------------------------

import { TriggerSmsFollowUpService } from '../TriggerSmsFollowUpService';
import type { SmsClient, Timer } from '../TriggerSmsFollowUpService';
import { smsLogger } from '@/server/logging/smsLogger';

const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// Test Helpers
// ---------------------------------------------------------------------------

function createMockClient(responses: Array<{ sid: string } | Error>): SmsClient {
  let callCount = 0;
  return {
    async sendMessage(_to: string, _body: string): Promise<{ sid: string }> {
      const response = responses[callCount++];
      if (response instanceof Error) throw response;
      return response;
    },
  };
}

const instantTimer: Timer = {
  async delay(_ms: number): Promise<void> {},
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TriggerSmsFollowUpService — Feedback Loop: Retry Behavior', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: transient failures → eventual success
  // -------------------------------------------------------------------------

  it('should succeed after 2 transient failures', async () => {
    // First 2 provider attempts throw transient error, 3rd succeeds
    const client = createMockClient([
      new Error('Transient network error'),
      new Error('Transient timeout'),
      { sid: 'SM-recovered-456' },
    ]);

    const result = await TriggerSmsFollowUpService.sendSms(
      'Test message',
      '+15551234567',
      client,
      instantTimer,
    );

    // Assert final status = success
    expect(result.status).toBe('sent');
    expect(result.messageId).toBe('SM-recovered-456');

    // Assert smsLogger.error called twice (for the two per-attempt failures)
    expect(mockLogger.error).toHaveBeenCalledTimes(2);
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: response conforms to SmsDeliveryResponseSchema
  // -------------------------------------------------------------------------

  it('should validate response conforms to SmsDeliveryResponseSchema', async () => {
    const client = createMockClient([
      new Error('Fail 1'),
      new Error('Fail 2'),
      { sid: 'SM-schema-check' },
    ]);

    const result = await TriggerSmsFollowUpService.sendSms(
      'Schema test',
      '+15559876543',
      client,
      instantTimer,
    );

    const parsed = SmsDeliveryResponseSchema.safeParse(result);
    expect(parsed.success).toBe(true);
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: max retry exhaustion → PROVIDER_FAILURE
  // -------------------------------------------------------------------------

  it('should throw PROVIDER_FAILURE after 3 consecutive failures', async () => {
    const client = createMockClient([
      new Error('Fail 1'),
      new Error('Fail 2'),
      new Error('Fail 3'),
    ]);

    try {
      await TriggerSmsFollowUpService.sendSms(
        'Fail test',
        '+15551234567',
        client,
        instantTimer,
      );
      expect.fail('Should have thrown');
    } catch (e) {
      expect(e).toBeInstanceOf(SmsError);
      expect((e as SmsError).code).toBe('PROVIDER_FAILURE');
    }

    // Assert error logs: 3 per-attempt (one per failed attempt)
    expect(mockLogger.error).toHaveBeenCalledTimes(3);
  });

  // -------------------------------------------------------------------------
  // Backoff timing enforcement
  // -------------------------------------------------------------------------

  it('should invoke timer.delay for backoff between retries', async () => {
    const delaySpy = vi.fn().mockResolvedValue(undefined);
    const mockTimer: Timer = { delay: delaySpy };

    const client = createMockClient([
      new Error('Fail 1'),
      new Error('Fail 2'),
      { sid: 'SM-backoff-test' },
    ]);

    await TriggerSmsFollowUpService.sendSms(
      'Backoff test',
      '+15551234567',
      client,
      mockTimer,
    );

    // Backoff: 1s after first failure, 2s after second failure
    expect(delaySpy).toHaveBeenCalledTimes(2);
    expect(delaySpy).toHaveBeenNthCalledWith(1, 1000);
    expect(delaySpy).toHaveBeenNthCalledWith(2, 2000);
  });

  it('should not invoke timer.delay when first attempt succeeds', async () => {
    const delaySpy = vi.fn().mockResolvedValue(undefined);
    const mockTimer: Timer = { delay: delaySpy };

    const client = createMockClient([{ sid: 'SM-first-try' }]);

    const result = await TriggerSmsFollowUpService.sendSms(
      'First try success',
      '+15551234567',
      client,
      mockTimer,
    );

    expect(result.status).toBe('sent');
    expect(delaySpy).not.toHaveBeenCalled();
    expect(mockLogger.error).not.toHaveBeenCalled();
  });

  it('should not invoke timer.delay after final failed attempt', async () => {
    const delaySpy = vi.fn().mockResolvedValue(undefined);
    const mockTimer: Timer = { delay: delaySpy };

    const client = createMockClient([
      new Error('Fail 1'),
      new Error('Fail 2'),
      new Error('Fail 3'),
    ]);

    try {
      await TriggerSmsFollowUpService.sendSms(
        'All fail test',
        '+15551234567',
        client,
        mockTimer,
      );
    } catch {
      // expected
    }

    // Backoff only between attempts 1→2 and 2→3, not after attempt 3
    expect(delaySpy).toHaveBeenCalledTimes(2);
    expect(delaySpy).toHaveBeenNthCalledWith(1, 1000);
    expect(delaySpy).toHaveBeenNthCalledWith(2, 2000);
  });

  // -------------------------------------------------------------------------
  // Error log context validation
  // -------------------------------------------------------------------------

  it('should log each failure attempt with phoneNumber context', async () => {
    const client = createMockClient([
      new Error('Network error'),
      { sid: 'SM-recovered' },
    ]);

    await TriggerSmsFollowUpService.sendSms(
      'Context check',
      '+15559999999',
      client,
      instantTimer,
    );

    expect(mockLogger.error).toHaveBeenCalledWith(
      expect.stringContaining('attempt 1'),
      expect.any(Error),
      expect.objectContaining({ phoneNumber: '+15559999999' }),
    );
  });
});
