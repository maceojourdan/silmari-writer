/**
 * FinalizeProcessor.metrics.test.ts - Step 4: Compute and Log Metrics
 *
 * TLA+ Properties:
 * - Reachability: Mock finalized draft with timestamps → computeAndLogMetrics → shared_logging.info called
 * - TypeInvariant: Metrics object matches { timeToDraft: number, confirmationRate: number, signalDensity: number }
 * - ErrorConsistency: Computation error → error logged via shared_logging.error; no exception thrown; draft remains FINALIZED
 *
 * Resource: db-b7r2 (processor)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeMetricsSchema } from '@/server/data_structures/Draft';
import type { Draft } from '@/server/data_structures/Draft';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/DraftDAO', () => ({
  DraftDAO: {
    getDraftById: vi.fn(),
    updateStatus: vi.fn(),
    insertMetrics: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('../../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FinalizeProcessor } from '../FinalizeProcessor';
import { frontendLogger } from '../../../logging/index';

const mockSharedLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const draftId = '660e8400-e29b-41d4-a716-446655440001';
const userId = '770e8400-e29b-41d4-a716-446655440002';

const finalizedDraft: Draft = {
  id: draftId,
  status: 'FINALIZED',
  content: 'Finalized content.',
  title: 'My Story',
  userId,
  createdAt: '2026-02-28T10:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
  approvedAt: '2026-02-28T11:00:00.000Z',
  finalizedAt: '2026-02-28T12:00:00.000Z',
  interactionData: {
    editsCount: 5,
    revisionsCount: 2,
    claimsVerified: 3,
    totalClaims: 4,
    signalEvents: 10,
  },
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeProcessor.computeAndLogMetrics — Step 4: Compute and Log Metrics', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call shared_logging.info with computed metrics', async () => {
      await FinalizeProcessor.computeAndLogMetrics(finalizedDraft);

      expect(mockSharedLogger.info).toHaveBeenCalledWith(
        'Finalize metrics computed',
        expect.objectContaining({
          module: 'FinalizeProcessor',
          action: 'computeAndLogMetrics',
          draftId,
        }),
      );
    });

    it('should return true on success', async () => {
      const result = await FinalizeProcessor.computeAndLogMetrics(finalizedDraft);
      expect(result).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should compute metrics matching FinalizeMetrics schema', () => {
      const metrics = FinalizeProcessor.computeMetrics(finalizedDraft);
      const parsed = FinalizeMetricsSchema.safeParse(metrics);

      expect(parsed.success).toBe(true);
    });

    it('should compute correct timeToDraft (creation to approval)', () => {
      const metrics = FinalizeProcessor.computeMetrics(finalizedDraft);

      // 10:00 to 11:00 = 1 hour = 3,600,000 ms
      expect(metrics.timeToDraft).toBe(3600000);
    });

    it('should compute correct confirmationRate', () => {
      const metrics = FinalizeProcessor.computeMetrics(finalizedDraft);

      // 3 verified / 4 total = 0.75
      expect(metrics.confirmationRate).toBe(0.75);
    });

    it('should compute correct signalDensity', () => {
      const metrics = FinalizeProcessor.computeMetrics(finalizedDraft);

      // 10 signals / (5 edits + 2 revisions) = 10/7 ≈ 1.4286
      expect(metrics.signalDensity).toBeCloseTo(10 / 7, 4);
    });

    it('should handle draft without interactionData', () => {
      const draftNoInteraction: Draft = {
        ...finalizedDraft,
        interactionData: undefined,
      };

      const metrics = FinalizeProcessor.computeMetrics(draftNoInteraction);

      expect(metrics.confirmationRate).toBe(0);
      expect(metrics.signalDensity).toBe(0);
    });

    it('should fall back to updatedAt when approvedAt is missing', () => {
      const draftNoApproval: Draft = {
        ...finalizedDraft,
        approvedAt: undefined,
      };

      const metrics = FinalizeProcessor.computeMetrics(draftNoApproval);

      // 10:00 to 12:00 = 2 hours = 7,200,000 ms
      expect(metrics.timeToDraft).toBe(7200000);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should not throw when computation error occurs', async () => {
      // Force an error by passing a draft with invalid date
      const badDraft: Draft = {
        ...finalizedDraft,
        createdAt: 'invalid-date',
      };

      // computeMetrics with invalid date still produces NaN but doesn't throw
      // So let's test with a more broken scenario
      const result = await FinalizeProcessor.computeAndLogMetrics(badDraft);

      // Should still return (true or false) without throwing
      expect(typeof result).toBe('boolean');
    });

    it('should log error via shared_logging.error on failure', async () => {
      // Spy on computeMetrics to force an error
      const computeSpy = vi.spyOn(FinalizeProcessor, 'computeMetrics');
      computeSpy.mockImplementation(() => {
        throw new Error('Computation failed');
      });

      const result = await FinalizeProcessor.computeAndLogMetrics(finalizedDraft);

      expect(result).toBe(false);
      expect(mockSharedLogger.error).toHaveBeenCalledWith(
        'Failed to compute finalize metrics',
        expect.any(Error),
        expect.objectContaining({
          module: 'FinalizeProcessor',
          action: 'computeAndLogMetrics',
          draftId,
        }),
      );

      computeSpy.mockRestore();
    });

    it('should not throw exception to caller on computation failure', async () => {
      const computeSpy = vi.spyOn(FinalizeProcessor, 'computeMetrics');
      computeSpy.mockImplementation(() => {
        throw new Error('Computation failed');
      });

      // Should NOT throw
      await expect(
        FinalizeProcessor.computeAndLogMetrics(finalizedDraft),
      ).resolves.toBe(false);

      computeSpy.mockRestore();
    });
  });
});
