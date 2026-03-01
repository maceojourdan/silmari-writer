/**
 * StoreSessionMetricsProcessChain.step4.test.ts - Step 4: Persist metrics record
 *
 * TLA+ Properties:
 * - Reachability: Mock DAO upsertSessionMetrics → persisted record returned
 * - TypeInvariant: Persisted object matches SessionMetrics structure
 * - ErrorConsistency: DAO throws → logger called + MetricsPersistenceError thrown
 *
 * Path: 301-store-session-metrics-on-pipeline-run
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoreSessionMetricsProcessChain } from '../StoreSessionMetricsProcessChain';
import { MetricsError } from '@/server/error_definitions/MetricsErrors';
import type { SessionMetrics } from '@/server/data_structures/SessionMetrics';

// ---------------------------------------------------------------------------
// Mock SessionMetricsDAO at the module boundary
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/SessionMetricsDAO', () => ({
  SessionMetricsDAO: {
    getSessionWithEvents: vi.fn(),
    upsertSessionMetrics: vi.fn(),
  },
}));

import { SessionMetricsDAO } from '@/server/data_access_objects/SessionMetricsDAO';
const mockDAO = vi.mocked(SessionMetricsDAO);

// ---------------------------------------------------------------------------
// Mock metricsLogger
// ---------------------------------------------------------------------------

vi.mock('../../logging/metricsLogger', () => ({
  metricsLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { metricsLogger } from '@/server/logging/metricsLogger';
const mockLogger = vi.mocked(metricsLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const computedMetrics = {
  timeToFirstDraft: 1_800_000,
  completionRate: 0.0909,
  confirmationRate: 0.5,
  signalDensity: 0.6667,
  dropOff: 0.9091,
};

const persistedMetrics: SessionMetrics = {
  id: '11111111-1111-1111-1111-111111111111',
  sessionId: validSessionId,
  ...computedMetrics,
  createdAt: '2026-02-28T12:05:00.000Z',
  updatedAt: '2026-02-28T12:05:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StoreSessionMetricsProcessChain.persistMetrics — Step 4: Persist metrics record', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return persisted record including sessionId and metric fields', async () => {
      mockDAO.upsertSessionMetrics.mockResolvedValue(persistedMetrics);

      const result = await StoreSessionMetricsProcessChain.persistMetrics(
        validSessionId,
        computedMetrics,
      );

      expect(result).toBeDefined();
      expect(result.sessionId).toBe(validSessionId);
      expect(result.timeToFirstDraft).toBe(computedMetrics.timeToFirstDraft);
      expect(result.completionRate).toBe(computedMetrics.completionRate);
      expect(result.confirmationRate).toBe(computedMetrics.confirmationRate);
      expect(result.signalDensity).toBe(computedMetrics.signalDensity);
      expect(result.dropOff).toBe(computedMetrics.dropOff);
      expect(mockDAO.upsertSessionMetrics).toHaveBeenCalledTimes(1);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return persisted object matching SessionMetrics structure', async () => {
      mockDAO.upsertSessionMetrics.mockResolvedValue(persistedMetrics);

      const result = await StoreSessionMetricsProcessChain.persistMetrics(
        validSessionId,
        computedMetrics,
      );

      expect(typeof result.sessionId).toBe('string');
      expect(typeof result.timeToFirstDraft).toBe('number');
      expect(typeof result.completionRate).toBe('number');
      expect(typeof result.confirmationRate).toBe('number');
      expect(typeof result.signalDensity).toBe('number');
      expect(typeof result.dropOff).toBe('number');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw METRICS_PERSISTENCE_ERROR when DAO throws', async () => {
      mockDAO.upsertSessionMetrics.mockRejectedValue(
        new Error('Database connection failed'),
      );

      try {
        await StoreSessionMetricsProcessChain.persistMetrics(
          validSessionId,
          computedMetrics,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('METRICS_PERSISTENCE_ERROR');
        expect((e as MetricsError).statusCode).toBe(500);
        expect((e as MetricsError).retryable).toBe(true);
      }
    });

    it('should call metricsLogger.error when DAO throws', async () => {
      const dbError = new Error('Database connection failed');
      mockDAO.upsertSessionMetrics.mockRejectedValue(dbError);

      try {
        await StoreSessionMetricsProcessChain.persistMetrics(
          validSessionId,
          computedMetrics,
        );
        expect.fail('Should have thrown');
      } catch {
        // Expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(1);
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('persist'),
        expect.any(Error),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });
  });
});
