/**
 * step5-record-result.test.ts - Step 5: Record SMS Delivery Result
 *
 * TLA+ Properties:
 * - Reachability: On success response → record stored (DAO.insert called), smsLogger.info called
 * - TypeInvariant: Stored entity passes SmsFollowUpRecordSchema.safeParse()
 * - ErrorConsistency: DAO throws → smsLogger.critical called, error re-thrown as SmsError PERSISTENCE_FAILURE
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { SmsDeliveryResponse } from '@/server/data_structures/FinalizeEvent';
import { SmsFollowUpRecordSchema } from '@/server/data_structures/SmsFollowUpRecord';
import { SmsError } from '@/server/error_definitions/SmsErrors';

// ---------------------------------------------------------------------------
// Mock DAO and Logger
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/SmsFollowUpDAO', () => ({
  SmsFollowUpDAO: {
    insert: vi.fn(),
  },
}));

vi.mock('@/server/logging/smsLogger', () => ({
  smsLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

import { SmsFollowUpDAO } from '../../data_access_objects/SmsFollowUpDAO';
import { smsLogger } from '@/server/logging/smsLogger';
import { TriggerSmsFollowUpService } from '../TriggerSmsFollowUpService';

const mockDAO = vi.mocked(SmsFollowUpDAO);
const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const phoneNumber = '+15551234567';
const message = 'Your answer has been finalized. Thank you!';

const successResponse: SmsDeliveryResponse = {
  status: 'sent',
  messageId: 'SM-abc123',
};

const storedRecord = {
  id: '770e8400-e29b-41d4-a716-446655440000',
  answerId,
  phoneNumber,
  message,
  status: 'sent' as const,
  messageId: 'SM-abc123',
  createdAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TriggerSmsFollowUpService.recordResult — Step 5: Record SMS Delivery Result', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DAO.insert and smsLogger.info on successful delivery response', async () => {
      mockDAO.insert.mockResolvedValue(storedRecord);

      const result = await TriggerSmsFollowUpService.recordResult(successResponse, answerId, phoneNumber, message);

      expect(mockDAO.insert).toHaveBeenCalledOnce();
      expect(mockDAO.insert).toHaveBeenCalledWith(
        expect.objectContaining({
          answerId,
          phoneNumber,
          message,
          status: 'sent',
        }),
      );
      expect(mockLogger.info).toHaveBeenCalled();
      expect(result).toBeDefined();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object passing SmsFollowUpRecordSchema validation', async () => {
      mockDAO.insert.mockResolvedValue(storedRecord);

      const result = await TriggerSmsFollowUpService.recordResult(successResponse, answerId, phoneNumber, message);
      const parsed = SmsFollowUpRecordSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should call smsLogger.critical and re-throw as SmsError with PERSISTENCE_FAILURE when DAO throws', async () => {
      mockDAO.insert.mockRejectedValue(new Error('Database write failed'));

      try {
        await TriggerSmsFollowUpService.recordResult(successResponse, answerId, phoneNumber, message);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('PERSISTENCE_FAILURE');
      }

      expect(mockLogger.critical).toHaveBeenCalled();
    });
  });
});
