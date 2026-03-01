/**
 * StoreSessionMetricsProcessChain.step5.test.ts - Step 5: Mark metrics pipeline success
 *
 * TLA+ Properties:
 * - Reachability: Call markSuccess(persistedMetrics) → { status: 'SUCCESS' }
 * - TypeInvariant: Returned state includes sessionId and status
 * - ErrorConsistency: Logger failure → MetricsPipelineOperationalError
 *
 * Path: 301-store-session-metrics-on-pipeline-run
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoreSessionMetricsProcessChain } from '../StoreSessionMetricsProcessChain';
import { MetricsError } from '@/server/error_definitions/MetricsErrors';
import type { SessionMetrics } from '@/server/data_structures/SessionMetrics';

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

const persistedMetrics: SessionMetrics = {
  id: '11111111-1111-1111-1111-111111111111',
  sessionId: validSessionId,
  timeToFirstDraft: 1_800_000,
  completionRate: 0.0909,
  confirmationRate: 0.5,
  signalDensity: 0.6667,
  dropOff: 0.9091,
  createdAt: '2026-02-28T12:05:00.000Z',
  updatedAt: '2026-02-28T12:05:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StoreSessionMetricsProcessChain.markSuccess — Step 5: Mark metrics pipeline success', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return success flag with status SUCCESS', () => {
      const result = StoreSessionMetricsProcessChain.markSuccess(persistedMetrics);

      expect(result).toBeDefined();
      expect(result.status).toBe('SUCCESS');
    });

    it('should call metricsLogger.info with pipeline completion message', () => {
      StoreSessionMetricsProcessChain.markSuccess(persistedMetrics);

      expect(mockLogger.info).toHaveBeenCalledTimes(1);
      expect(mockLogger.info).toHaveBeenCalledWith(
        expect.stringContaining('completed successfully'),
        expect.objectContaining({
          sessionId: validSessionId,
          timeToFirstDraft: persistedMetrics.timeToFirstDraft,
          completionRate: persistedMetrics.completionRate,
        }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object with sessionId and status fields', () => {
      const result = StoreSessionMetricsProcessChain.markSuccess(persistedMetrics);

      expect(typeof result.sessionId).toBe('string');
      expect(result.sessionId).toBe(validSessionId);
      expect(result.status).toBe('SUCCESS');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw METRICS_PIPELINE_OPERATIONAL_ERROR when logger throws', () => {
      mockLogger.info.mockImplementation(() => {
        throw new Error('Logger connection failed');
      });

      try {
        StoreSessionMetricsProcessChain.markSuccess(persistedMetrics);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('METRICS_PIPELINE_OPERATIONAL_ERROR');
        expect((e as MetricsError).statusCode).toBe(500);
        expect((e as MetricsError).retryable).toBe(true);
      }
    });
  });
});
