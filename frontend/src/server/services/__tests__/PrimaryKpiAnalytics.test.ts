/**
 * PrimaryKpiAnalytics.test.ts - Step 4: Trigger analytics event emission
 *
 * TLA+ Properties:
 * - Reachability: valid record -> assert `sendAnalyticsEvent()` called once
 * - TypeInvariant: payload matches `AnalyticsEventPayload` type
 * - ErrorConsistency:
 *     - Payload transform throws -> assert logger.error called, no external call
 *     - External fails twice then succeeds -> assert 3 attempts max
 *     - External fails 3 times -> assert logger.error("final_failure")
 *
 * Resource: db-h2s4 (service)
 * Path: 339-record-primary-kpi-analytics-event
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  AnalyticsEventPayloadSchema,
} from '@/server/data_structures/PrimaryKpiRecord';
import type {
  PrimaryKpiRecord,
  AnalyticsEventPayload,
} from '@/server/data_structures/PrimaryKpiRecord';
import { KpiError } from '@/server/error_definitions/KpiErrors';

// ---------------------------------------------------------------------------
// Mock DAO (database boundary)
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/PrimaryKpiDAO', () => ({
  PrimaryKpiDAO: {
    insert: vi.fn(),
    findById: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock kpiLogger (logging boundary)
// ---------------------------------------------------------------------------

vi.mock('@/server/logging/kpiLogger', () => ({
  kpiLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock analytics client (external analytics boundary)
// ---------------------------------------------------------------------------

vi.mock('../analyticsClient', () => ({
  sendAnalyticsEvent: vi.fn(),
}));

// ---------------------------------------------------------------------------
// Imports (must come after vi.mock)
// ---------------------------------------------------------------------------

import { PrimaryKpiDAO } from '../../data_access_objects/PrimaryKpiDAO';
import { kpiLogger } from '@/server/logging/kpiLogger';
import { sendAnalyticsEvent } from '../analyticsClient';
import { PrimaryKpiService } from '../PrimaryKpiService';

const mockDAO = vi.mocked(PrimaryKpiDAO);
const mockLogger = vi.mocked(kpiLogger);
const mockSendAnalytics = vi.mocked(sendAnalyticsEvent);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const persistedRecord: PrimaryKpiRecord = {
  id: '550e8400-e29b-41d4-a716-446655440001',
  userId: 'user-001',
  actionType: 'purchase',
  metadata: { amount: 99.99, currency: 'USD' },
  status: 'PERSISTED',
  timestamp: '2026-03-01T14:30:00.000Z',
  createdAt: '2026-03-01T14:30:01.000Z',
};

const expectedPayload: AnalyticsEventPayload = {
  eventId: persistedRecord.id,
  userId: persistedRecord.userId,
  actionType: persistedRecord.actionType,
  metadata: persistedRecord.metadata,
  timestamp: persistedRecord.timestamp,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('PrimaryKpiService.emitAnalytics — Step 4: Trigger analytics event emission', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call sendAnalyticsEvent once for a valid persisted record', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockSendAnalytics).toHaveBeenCalledTimes(1);
    });

    it('should return true when analytics emission succeeds', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(result).toBe(true);
    });

    it('should pass correct payload fields to sendAnalyticsEvent', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      const calledPayload = mockSendAnalytics.mock.calls[0][0];
      expect(calledPayload.eventId).toBe(persistedRecord.id);
      expect(calledPayload.userId).toBe(persistedRecord.userId);
      expect(calledPayload.actionType).toBe(persistedRecord.actionType);
      expect(calledPayload.metadata).toEqual(persistedRecord.metadata);
      expect(calledPayload.timestamp).toBe(persistedRecord.timestamp);
    });

    it('should update record status to ANALYTICS_SENT on success', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_SENT',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockDAO.updateStatus).toHaveBeenCalledWith(
        persistedRecord.id,
        'ANALYTICS_SENT',
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should construct payload matching AnalyticsEventPayloadSchema', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      const calledPayload = mockSendAnalytics.mock.calls[0][0];
      const parsed = AnalyticsEventPayloadSchema.safeParse(calledPayload);

      expect(parsed.success).toBe(true);
    });

    it('should preserve metadata structure from the record in the payload', async () => {
      const recordWithComplexMetadata: PrimaryKpiRecord = {
        ...persistedRecord,
        metadata: { items: ['a', 'b'], total: 200, nested: { key: 'value' } },
      };
      mockSendAnalytics.mockResolvedValue(undefined);

      await PrimaryKpiService.emitAnalytics(recordWithComplexMetadata);

      const calledPayload = mockSendAnalytics.mock.calls[0][0];
      const parsed = AnalyticsEventPayloadSchema.safeParse(calledPayload);

      expect(parsed.success).toBe(true);
      expect(calledPayload.metadata).toEqual(recordWithComplexMetadata.metadata);
    });

    it('should include eventId as a valid UUID from the record id', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      const calledPayload = mockSendAnalytics.mock.calls[0][0];
      const uuidRegex =
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
      expect(calledPayload.eventId).toMatch(uuidRegex);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log error and not call sendAnalyticsEvent when payload transform throws', async () => {
      // Pass a record with missing required fields to cause transform failure
      const malformedRecord = {
        ...persistedRecord,
        id: '', // invalid: empty string fails UUID validation in transform
        userId: '',
      } as PrimaryKpiRecord;

      const result = await PrimaryKpiService.emitAnalytics(malformedRecord);

      expect(mockLogger.error).toHaveBeenCalled();
      expect(mockSendAnalytics).not.toHaveBeenCalled();
      expect(result).toBe(false);
    });

    it('should include transform error context in logger.error call', async () => {
      const malformedRecord = {
        ...persistedRecord,
        id: '',
        userId: '',
      } as PrimaryKpiRecord;

      await PrimaryKpiService.emitAnalytics(malformedRecord);

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.any(String),
        expect.any(Error),
        expect.objectContaining({
          recordId: malformedRecord.id,
        }),
      );
    });

    it('should succeed after 2 transient failures followed by success (3 attempts)', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Network timeout'))
        .mockRejectedValueOnce(new Error('Network timeout'))
        .mockResolvedValueOnce(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_SENT',
      });

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(result).toBe(true);
      expect(mockSendAnalytics).toHaveBeenCalledTimes(3);
    });

    it('should not exceed 3 attempts when external call keeps failing', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Attempt 1 failed'))
        .mockRejectedValueOnce(new Error('Attempt 2 failed'))
        .mockRejectedValueOnce(new Error('Attempt 3 failed'));

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockSendAnalytics).toHaveBeenCalledTimes(3);
    });

    it('should log "final_failure" when all 3 attempts fail', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Fail 1'))
        .mockRejectedValueOnce(new Error('Fail 2'))
        .mockRejectedValueOnce(new Error('Fail 3'));

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('final_failure'),
        expect.any(Error),
        expect.objectContaining({
          recordId: persistedRecord.id,
        }),
      );
    });

    it('should return false when all 3 attempts fail', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Fail 1'))
        .mockRejectedValueOnce(new Error('Fail 2'))
        .mockRejectedValueOnce(new Error('Fail 3'));

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(result).toBe(false);
    });

    it('should update record status to ANALYTICS_FAILED when all attempts fail', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Fail 1'))
        .mockRejectedValueOnce(new Error('Fail 2'))
        .mockRejectedValueOnce(new Error('Fail 3'));
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockDAO.updateStatus).toHaveBeenCalledWith(
        persistedRecord.id,
        'ANALYTICS_FAILED',
      );
    });

    it('should not log "final_failure" when retries eventually succeed', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Transient'))
        .mockResolvedValueOnce(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_SENT',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      const finalFailureCalls = mockLogger.error.mock.calls.filter(
        ([msg]) => typeof msg === 'string' && msg.includes('final_failure'),
      );
      expect(finalFailureCalls).toHaveLength(0);
    });

    it('should not call sendAnalyticsEvent after transform error even if client is healthy', async () => {
      const malformedRecord = {
        ...persistedRecord,
        id: '',
        userId: '',
      } as PrimaryKpiRecord;

      mockSendAnalytics.mockResolvedValue(undefined);

      await PrimaryKpiService.emitAnalytics(malformedRecord);

      expect(mockSendAnalytics).not.toHaveBeenCalled();
    });
  });
});
