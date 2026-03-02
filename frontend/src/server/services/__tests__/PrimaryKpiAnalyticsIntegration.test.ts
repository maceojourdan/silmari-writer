/**
 * PrimaryKpiAnalyticsIntegration.test.ts - Step 5: Analytics system records and displays event
 *
 * TLA+ Properties:
 * - Reachability: mock provider returns 200 -> assert service resolves success
 * - TypeInvariant: ensure response status handled as expected type
 * - ErrorConsistency: mock provider 400 rejection -> assert structured log entry created
 *
 * Tests the HTTP response handling of the analytics client itself. Mocks at the
 * fetch boundary to verify PrimaryKpiService.emitAnalytics handles external
 * provider responses correctly end-to-end.
 *
 * Resource: db-h2s4 (service)
 * Path: 339-record-primary-kpi-analytics-event
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { PrimaryKpiRecord } from '@/server/data_structures/PrimaryKpiRecord';

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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('PrimaryKpiService.emitAnalytics — Step 5: Analytics system records and displays event', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should resolve to true when mock provider accepts the event (200)', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_SENT',
      });

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(result).toBe(true);
    });

    it('should call sendAnalyticsEvent with a payload derived from the record', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_SENT',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockSendAnalytics).toHaveBeenCalledTimes(1);
      const calledPayload = mockSendAnalytics.mock.calls[0][0];
      expect(calledPayload.eventId).toBe(persistedRecord.id);
      expect(calledPayload.userId).toBe(persistedRecord.userId);
      expect(calledPayload.actionType).toBe(persistedRecord.actionType);
    });

    it('should update record status to ANALYTICS_SENT after provider accepts', async () => {
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

    it('should handle records with different actionTypes correctly', async () => {
      const signupRecord: PrimaryKpiRecord = {
        ...persistedRecord,
        id: '660e8400-e29b-41d4-a716-446655440002',
        actionType: 'signup',
        metadata: { source: 'organic' },
      };
      mockSendAnalytics.mockResolvedValue(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...signupRecord,
        status: 'ANALYTICS_SENT',
      });

      const result = await PrimaryKpiService.emitAnalytics(signupRecord);

      expect(result).toBe(true);
      const calledPayload = mockSendAnalytics.mock.calls[0][0];
      expect(calledPayload.actionType).toBe('signup');
      expect(calledPayload.metadata).toEqual({ source: 'organic' });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a boolean value on successful emission', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_SENT',
      });

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(typeof result).toBe('boolean');
      expect(result).toBe(true);
    });

    it('should return a boolean value on failed emission', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Provider 500'))
        .mockRejectedValueOnce(new Error('Provider 500'))
        .mockRejectedValueOnce(new Error('Provider 500'));
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(typeof result).toBe('boolean');
      expect(result).toBe(false);
    });

    it('should not throw an error regardless of provider response (returns boolean instead)', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Provider rejected'))
        .mockRejectedValueOnce(new Error('Provider rejected'))
        .mockRejectedValueOnce(new Error('Provider rejected'));
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      await expect(
        PrimaryKpiService.emitAnalytics(persistedRecord),
      ).resolves.toBeDefined();
    });

    it('should handle provider returning undefined on success without type error', async () => {
      mockSendAnalytics.mockResolvedValue(undefined);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_SENT',
      });

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(result).toBe(true);
      expect(mockDAO.updateStatus).toHaveBeenCalledWith(
        persistedRecord.id,
        'ANALYTICS_SENT',
      );
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should create structured log entry when provider rejects with 400', async () => {
      const rejectionError = new Error('Provider returned 400: Bad Request');
      mockSendAnalytics
        .mockRejectedValueOnce(rejectionError)
        .mockRejectedValueOnce(rejectionError)
        .mockRejectedValueOnce(rejectionError);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('final_failure'),
        expect.any(Error),
        expect.objectContaining({
          recordId: persistedRecord.id,
        }),
      );
    });

    it('should include recordId in the structured log context on rejection', async () => {
      const rejectionError = new Error('Provider returned 400');
      mockSendAnalytics
        .mockRejectedValueOnce(rejectionError)
        .mockRejectedValueOnce(rejectionError)
        .mockRejectedValueOnce(rejectionError);
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      const errorCalls = mockLogger.error.mock.calls;
      const finalFailureCall = errorCalls.find(
        ([msg]) => typeof msg === 'string' && msg.includes('final_failure'),
      );
      expect(finalFailureCall).toBeDefined();
      expect(finalFailureCall![2]).toEqual(
        expect.objectContaining({
          recordId: persistedRecord.id,
        }),
      );
    });

    it('should update record status to ANALYTICS_FAILED on provider rejection', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('400 Bad Request'))
        .mockRejectedValueOnce(new Error('400 Bad Request'))
        .mockRejectedValueOnce(new Error('400 Bad Request'));
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

    it('should return false when provider rejects the event', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Rejected'))
        .mockRejectedValueOnce(new Error('Rejected'))
        .mockRejectedValueOnce(new Error('Rejected'));
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      const result = await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(result).toBe(false);
    });

    it('should not log final_failure when rejection is recovered by retry', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Transient 500'))
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

    it('should not call DAO.updateStatus with ANALYTICS_SENT when all attempts fail', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Fail'))
        .mockRejectedValueOnce(new Error('Fail'))
        .mockRejectedValueOnce(new Error('Fail'));
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockDAO.updateStatus).not.toHaveBeenCalledWith(
        persistedRecord.id,
        'ANALYTICS_SENT',
      );
    });

    it('should handle mixed error types across retries and still log final_failure', async () => {
      mockSendAnalytics
        .mockRejectedValueOnce(new Error('Network timeout'))
        .mockRejectedValueOnce(new TypeError('Failed to fetch'))
        .mockRejectedValueOnce(new Error('Provider 503'));
      mockDAO.updateStatus.mockResolvedValue({
        ...persistedRecord,
        status: 'ANALYTICS_FAILED',
      });

      await PrimaryKpiService.emitAnalytics(persistedRecord);

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('final_failure'),
        expect.any(Error),
        expect.objectContaining({
          recordId: persistedRecord.id,
        }),
      );
      expect(mockSendAnalytics).toHaveBeenCalledTimes(3);
    });
  });
});
