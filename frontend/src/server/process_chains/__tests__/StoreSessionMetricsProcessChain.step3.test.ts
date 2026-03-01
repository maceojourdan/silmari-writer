/**
 * StoreSessionMetricsProcessChain.step3.test.ts - Step 3: Compute session metrics
 *
 * TLA+ Properties:
 * - Reachability: Valid dataset with timestamps + events → metrics object with all five fields
 * - TypeInvariant: All five metric fields are numeric
 * - ErrorConsistency: Dataset missing required timestamps → InvalidMetricsInputError
 *
 * Path: 301-store-session-metrics-on-pipeline-run
 */

import { describe, it, expect } from 'vitest';
import { StoreSessionMetricsProcessChain } from '../StoreSessionMetricsProcessChain';
import { MetricsError } from '@/server/error_definitions/MetricsErrors';
import type { AggregatedSessionDataset } from '@/server/data_structures/SessionMetrics';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const validDataset: AggregatedSessionDataset = {
  session: {
    id: validSessionId,
    status: 'FINALIZED',
    createdAt: '2026-02-28T10:00:00.000Z',
    updatedAt: '2026-02-28T12:00:00.000Z',
    firstDraftAt: '2026-02-28T10:30:00.000Z',
    finalizedAt: '2026-02-28T12:00:00.000Z',
  },
  events: [
    // 2 DRAFT events
    { id: '00000001-0000-1000-8000-000000000001', sessionId: validSessionId, category: 'DRAFT', timestamp: '2026-02-28T10:30:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000002', sessionId: validSessionId, category: 'DRAFT', timestamp: '2026-02-28T10:35:00.000Z' },
    // 3 VERIFY events
    { id: '00000001-0000-1000-8000-000000000003', sessionId: validSessionId, category: 'VERIFY', timestamp: '2026-02-28T11:00:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000004', sessionId: validSessionId, category: 'VERIFY', timestamp: '2026-02-28T11:10:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000005', sessionId: validSessionId, category: 'VERIFY', timestamp: '2026-02-28T11:20:00.000Z' },
    // 1 FINALIZE event
    { id: '00000001-0000-1000-8000-000000000006', sessionId: validSessionId, category: 'FINALIZE', timestamp: '2026-02-28T12:00:00.000Z' },
    // 2 EDIT events
    { id: '00000001-0000-1000-8000-000000000007', sessionId: validSessionId, category: 'EDIT', timestamp: '2026-02-28T10:40:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000008', sessionId: validSessionId, category: 'EDIT', timestamp: '2026-02-28T10:50:00.000Z' },
    // 1 REVISION event
    { id: '00000001-0000-1000-8000-000000000009', sessionId: validSessionId, category: 'REVISION', timestamp: '2026-02-28T11:30:00.000Z' },
    // 2 SIGNAL events
    { id: '00000001-0000-1000-8000-000000000010', sessionId: validSessionId, category: 'SIGNAL', timestamp: '2026-02-28T11:05:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000011', sessionId: validSessionId, category: 'SIGNAL', timestamp: '2026-02-28T11:15:00.000Z' },
  ],
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StoreSessionMetricsProcessChain.computeMetrics — Step 3: Compute session metrics', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return metrics object containing all five fields', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      expect(metrics).toBeDefined();
      expect(metrics).toHaveProperty('timeToFirstDraft');
      expect(metrics).toHaveProperty('completionRate');
      expect(metrics).toHaveProperty('confirmationRate');
      expect(metrics).toHaveProperty('signalDensity');
      expect(metrics).toHaveProperty('dropOff');
    });

    it('should compute correct timeToFirstDraft (ms from createdAt to firstDraftAt)', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      // 10:00 to 10:30 = 30 minutes = 1,800,000 ms
      expect(metrics.timeToFirstDraft).toBe(1_800_000);
    });

    it('should compute correct completionRate (FINALIZE events / total events)', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      // 1 FINALIZE / 11 total events = ~0.0909
      expect(metrics.completionRate).toBeCloseTo(1 / 11, 4);
    });

    it('should compute correct confirmationRate (VERIFY events / (DRAFT + VERIFY + FINALIZE) events)', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      // 3 VERIFY / (2 DRAFT + 3 VERIFY + 1 FINALIZE) = 3/6 = 0.5
      expect(metrics.confirmationRate).toBeCloseTo(3 / 6, 4);
    });

    it('should compute correct signalDensity (SIGNAL events / (EDIT + REVISION) events)', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      // 2 SIGNAL / (2 EDIT + 1 REVISION) = 2/3 = ~0.6667
      expect(metrics.signalDensity).toBeCloseTo(2 / 3, 4);
    });

    it('should compute correct dropOff (1 - completionRate)', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      // dropOff = 1 - (1/11) = 10/11 = ~0.9091
      expect(metrics.dropOff).toBeCloseTo(1 - (1 / 11), 4);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return all five metric fields as numbers', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      expect(typeof metrics.timeToFirstDraft).toBe('number');
      expect(typeof metrics.completionRate).toBe('number');
      expect(typeof metrics.confirmationRate).toBe('number');
      expect(typeof metrics.signalDensity).toBe('number');
      expect(typeof metrics.dropOff).toBe('number');
    });

    it('should return rates between 0 and 1 (inclusive)', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      expect(metrics.completionRate).toBeGreaterThanOrEqual(0);
      expect(metrics.completionRate).toBeLessThanOrEqual(1);
      expect(metrics.confirmationRate).toBeGreaterThanOrEqual(0);
      expect(metrics.confirmationRate).toBeLessThanOrEqual(1);
      expect(metrics.signalDensity).toBeGreaterThanOrEqual(0);
      expect(metrics.signalDensity).toBeLessThanOrEqual(1);
      expect(metrics.dropOff).toBeGreaterThanOrEqual(0);
      expect(metrics.dropOff).toBeLessThanOrEqual(1);
    });

    it('should return non-negative timeToFirstDraft', () => {
      const metrics = StoreSessionMetricsProcessChain.computeMetrics(validDataset);

      expect(metrics.timeToFirstDraft).toBeGreaterThanOrEqual(0);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw INVALID_METRICS_INPUT when dataset is missing firstDraftAt', () => {
      const datasetMissingFirstDraft: AggregatedSessionDataset = {
        session: {
          ...validDataset.session,
          firstDraftAt: undefined,
        },
        events: validDataset.events,
      };

      try {
        StoreSessionMetricsProcessChain.computeMetrics(datasetMissingFirstDraft);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('INVALID_METRICS_INPUT');
        expect((e as MetricsError).statusCode).toBe(422);
      }
    });

    it('should throw INVALID_METRICS_INPUT when dataset is missing finalizedAt', () => {
      const datasetMissingFinalized: AggregatedSessionDataset = {
        session: {
          ...validDataset.session,
          finalizedAt: undefined,
        },
        events: validDataset.events,
      };

      try {
        StoreSessionMetricsProcessChain.computeMetrics(datasetMissingFinalized);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('INVALID_METRICS_INPUT');
        expect((e as MetricsError).statusCode).toBe(422);
      }
    });

    it('should throw INVALID_METRICS_INPUT when events array is empty', () => {
      const datasetEmptyEvents: AggregatedSessionDataset = {
        session: validDataset.session,
        events: [],
      };

      try {
        StoreSessionMetricsProcessChain.computeMetrics(datasetEmptyEvents);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('INVALID_METRICS_INPUT');
        expect((e as MetricsError).statusCode).toBe(422);
      }
    });
  });

  // -------------------------------------------------------------------------
  // Edge cases
  // -------------------------------------------------------------------------

  describe('Edge cases', () => {
    it('should return signalDensity of 0 when no EDIT or REVISION events exist', () => {
      const datasetNoEdits: AggregatedSessionDataset = {
        session: validDataset.session,
        events: [
          { id: '00000001-0000-1000-8000-000000000020', sessionId: validSessionId, category: 'DRAFT', timestamp: '2026-02-28T10:30:00.000Z' },
          { id: '00000001-0000-1000-8000-000000000021', sessionId: validSessionId, category: 'VERIFY', timestamp: '2026-02-28T11:00:00.000Z' },
          { id: '00000001-0000-1000-8000-000000000022', sessionId: validSessionId, category: 'FINALIZE', timestamp: '2026-02-28T12:00:00.000Z' },
        ],
      };

      const metrics = StoreSessionMetricsProcessChain.computeMetrics(datasetNoEdits);

      expect(metrics.signalDensity).toBe(0);
    });

    it('should return confirmationRate of 0 when no workflow events exist', () => {
      const datasetOnlyEdits: AggregatedSessionDataset = {
        session: validDataset.session,
        events: [
          { id: '00000001-0000-1000-8000-000000000030', sessionId: validSessionId, category: 'EDIT', timestamp: '2026-02-28T10:30:00.000Z' },
          { id: '00000001-0000-1000-8000-000000000031', sessionId: validSessionId, category: 'SIGNAL', timestamp: '2026-02-28T11:00:00.000Z' },
        ],
      };

      const metrics = StoreSessionMetricsProcessChain.computeMetrics(datasetOnlyEdits);

      expect(metrics.confirmationRate).toBe(0);
    });
  });
});
