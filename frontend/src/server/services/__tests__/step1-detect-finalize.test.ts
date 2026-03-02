/**
 * step1-detect-finalize.test.ts - Step 1: Detect Finalize Completion
 *
 * TLA+ Properties:
 * - Reachability: Given event with smsOptIn:true and valid phone → returns { shouldSend: true, answerId, phoneNumber }
 * - TypeInvariant: Returned object passes DetectFinalizeResultSchema.safeParse()
 * - ErrorConsistency (opt-out): smsOptIn:false → returns { shouldSend: false } (no throw)
 * - ErrorConsistency (missing phone): smsOptIn:true but missing/invalid phone → throws SharedError MISSING_PHONE_NUMBER 422
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { FinalizeEvent } from '@/server/data_structures/FinalizeEvent';
import { DetectFinalizeResultSchema } from '@/server/data_structures/FinalizeEvent';
import { SharedError } from '@/server/error_definitions/SharedErrors';

import { TriggerSmsFollowUpService } from '../TriggerSmsFollowUpService';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const userId = '660e8400-e29b-41d4-a716-446655440000';

const optInEvent: FinalizeEvent = {
  answerId,
  userId,
  smsOptIn: true,
  phoneNumber: '+15551234567',
};

const optOutEvent: FinalizeEvent = {
  answerId,
  userId,
  smsOptIn: false,
  phoneNumber: '+15551234567',
};

const missingPhoneEvent: FinalizeEvent = {
  answerId,
  userId,
  smsOptIn: true,
  phoneNumber: undefined,
};

const emptyPhoneEvent: FinalizeEvent = {
  answerId,
  userId,
  smsOptIn: true,
  phoneNumber: '',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TriggerSmsFollowUpService.detectFinalizeCompletion — Step 1: Detect Finalize Completion', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return { shouldSend: true, answerId, phoneNumber } when smsOptIn is true and phone is valid', () => {
      const result = TriggerSmsFollowUpService.detectFinalizeCompletion(optInEvent);

      expect(result).toEqual({
        shouldSend: true,
        answerId,
        phoneNumber: '+15551234567',
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object passing DetectFinalizeResultSchema validation when opted in', () => {
      const result = TriggerSmsFollowUpService.detectFinalizeCompletion(optInEvent);
      const parsed = DetectFinalizeResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });

    it('should return object passing DetectFinalizeResultSchema validation when opted out', () => {
      const result = TriggerSmsFollowUpService.detectFinalizeCompletion(optOutEvent);
      const parsed = DetectFinalizeResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return { shouldSend: false } when smsOptIn is false (no throw)', () => {
      const result = TriggerSmsFollowUpService.detectFinalizeCompletion(optOutEvent);

      expect(result).toEqual({ shouldSend: false });
    });

    it('should throw SharedError with code MISSING_PHONE_NUMBER when smsOptIn is true but phone is undefined', () => {
      try {
        TriggerSmsFollowUpService.detectFinalizeCompletion(missingPhoneEvent);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SharedError);
        expect((e as SharedError).code).toBe('MISSING_PHONE_NUMBER');
        expect((e as SharedError).statusCode).toBe(422);
      }
    });

    it('should throw SharedError with code MISSING_PHONE_NUMBER when smsOptIn is true but phone is empty string', () => {
      try {
        TriggerSmsFollowUpService.detectFinalizeCompletion(emptyPhoneEvent);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SharedError);
        expect((e as SharedError).code).toBe('MISSING_PHONE_NUMBER');
        expect((e as SharedError).statusCode).toBe(422);
      }
    });
  });
});
